import HSFormal.LTheory.Model.CZFunctor

/-!
# Karoubi filtrations of `C_ℤ(A)` (lower L-theory model, module 3)

For a Karoubi filtration `F : U ⊂ A` ([CP95, 1.27], `KaroubiFiltration`), `F.cz` is the
Karoubi filtration `C_ℤ(U) ⊂ C_ℤ(A)`:

* `U' = CZ.indexwise F.U`: all entries lie in `U`;
* the splittings of `X` are the indexwise ones `CZ.diagSplitting σ` (`F.czSplittings X`), `σ v`
  a splitting of `X_v` in the family of `F` (diagonal, hence of propagation `0`); they are
  self-dual since those of `F` are;
* factorization: a bounded matrix all of whose entries lie in `I_U` factors through a single
  indexwise splitting (`exists_row`, `exists_col`): the window of a row/column is finite, so
  finitely many splittings of `X_w` are dominated by one (`exists_forall_of_directed`); the
  factorization `f = (f ≫ πE) ≫ ιE` keeps the propagation of `f`;
* the sum axiom holds for *every* bilimit bicone of `C_ℤ(A)`, as it follows formally from the
  other axioms in any preadditive category (`HSFormal.KaroubiFiltration.ofFactor`).

Hence `I_{U'}` is exactly the set of bounded matrices with entries in `I_U`
(`factorsThrough_cz_iff`), and there are strict `InvCat` isomorphisms
`F.czSubIso : F.cz.sub ≅ F.sub.cz` and `F.czQuotIso : F.cz.quot ≅ F.quot.cz` compatible with
inclusions and projections.  `FiltrationHom.cz` is functorial and compatible with both isos;
`F.czRestrictHom`/`F.czRestrictInv` identify `(F.cz).restrict (indexwise V)` with
`(F.restrict V).cz` (via the strict iso `CZ.subIso V`).  The iterates are `F.czIter k`,
`Φ.czIter k`, `F.czIterSubIso k`, `F.czIterQuotIso k` (built with `CZ.mapIso`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive

noncomputable section

/-! ### Generic facts on Karoubi filtrations -/

section Generic

variable {C : Type*} [Category C] [Preadditive C] {𝒰 : ObjectProperty C} {X : C}

omit [Preadditive C] in
lemma IdemLE.trans {e e' e'' : X ⟶ X} (h : IdemLE e e') (h' : IdemLE e' e'') : IdemLE e e'' :=
  ⟨by rw [← h.1, assoc, h'.1], by rw [← h.2, ← assoc, h'.2]⟩

/-- A condition on splittings stable under enlarging the splitting. -/
def UpClosed (P : Splitting X → Prop) : Prop :=
  ∀ σ ρ : Splitting X, P σ → IdemLE σ.idem ρ.idem → P ρ

lemma upClosed_absorbR {V : C} (f : V ⟶ X) : UpClosed fun σ : Splitting X ↦ f ≫ σ.idem = f :=
  fun σ ρ (h : f ≫ σ.idem = f) hle ↦ show f ≫ ρ.idem = f by rw [← h, assoc, hle.1]

lemma upClosed_absorbL {V : C} (g : X ⟶ V) : UpClosed fun σ : Splitting X ↦ σ.idem ≫ g = g :=
  fun σ ρ (h : σ.idem ≫ g = g) hle ↦ show ρ.idem ≫ g = g by rw [← h, ← assoc, hle.2]

/-- A map factoring through `ιE` is absorbed by the idempotent. -/
lemma absorbR_of_eq {V : C} {f : V ⟶ X} {σ : Splitting X} {g : V ⟶ σ.E} (h : f = g ≫ σ.ιE) :
    f ≫ σ.idem = f := by
  rw [h, Splitting.idem, assoc, ← assoc σ.ιE, σ.ιE_πE, id_comp]

/-- A map factoring through `πE` is absorbed by the idempotent. -/
lemma absorbL_of_eq {V : C} {f : X ⟶ V} {σ : Splitting X} {g : σ.E ⟶ V} (h : f = σ.πE ≫ g) :
    σ.idem ≫ f = f := by
  rw [h, Splitting.idem, assoc, ← assoc σ.ιE, σ.ιE_πE, id_comp]

section Directed

variable {S : Set (Splitting X)}
  (hd : ∀ σ ∈ S, ∀ τ ∈ S, ∃ ρ ∈ S, IdemLE σ.idem ρ.idem ∧ IdemLE τ.idem ρ.idem)
include hd

/-- Two up-closed conditions satisfiable in a directed family are simultaneously satisfiable. -/
lemma exists_and_of_directed {P Q : Splitting X → Prop} (hP : UpClosed P) (hQ : UpClosed Q)
    (h₁ : ∃ σ ∈ S, P σ) (h₂ : ∃ σ ∈ S, Q σ) : ∃ ρ ∈ S, P ρ ∧ Q ρ := by
  obtain ⟨σ, hσ, hPσ⟩ := h₁
  obtain ⟨τ, hτ, hQτ⟩ := h₂
  obtain ⟨ρ, hρ, h, h'⟩ := hd σ hσ τ hτ
  exact ⟨ρ, hρ, hP σ ρ hPσ h, hQ τ ρ hQτ h'⟩

/-- Finitely many up-closed conditions satisfiable in a nonempty directed family are
simultaneously satisfiable. -/
lemma exists_forall_of_directed (hne : S.Nonempty) {ι : Type*} (s : Finset ι)
    {P : ι → Splitting X → Prop} (hP : ∀ i, UpClosed (P i)) (h : ∀ i ∈ s, ∃ σ ∈ S, P i σ) :
    ∃ ρ ∈ S, ∀ i ∈ s, P i ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hne.some, hne.some_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ρ, hρ, hρ'⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    obtain ⟨σ, hσ, h₁, h₂⟩ := exists_and_of_directed hd (P := fun ρ ↦ ∀ i ∈ s, P i ρ)
      (fun σ ρ h hle i hi ↦ hP i σ ρ (h i hi) hle) (hP a) ⟨ρ, hρ, hρ'⟩
      (h a (Finset.mem_insert_self a s))
    refine ⟨σ, hσ, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₂
    · exact h₁ i hi

end Directed

variable (𝒰) in
/-- [CP95, 1.27] from axioms (i)–(iii): the sum axiom (iv) is a formal consequence of the
factorization axioms and directedness, for every bilimit bicone. -/
def _root_.HSFormal.KaroubiFiltration.ofFactor (splittings : ∀ X : C, Set (Splitting X)) (mem : ∀ X, ∀ σ ∈ splittings X, 𝒰 σ.E)
    (nonempty : ∀ X, (splittings X).Nonempty)
    (directed : ∀ X, ∀ σ ∈ splittings X, ∀ τ ∈ splittings X,
      ∃ ρ ∈ splittings X, IdemLE σ.idem ρ.idem ∧ IdemLE τ.idem ρ.idem)
    (factor_to : ∀ {V X : C}, 𝒰 V → ∀ f : V ⟶ X,
      ∃ σ ∈ splittings X, ∃ g : V ⟶ σ.E, f = g ≫ σ.ιE)
    (factor_from : ∀ {X V : C}, 𝒰 V → ∀ f : X ⟶ V,
      ∃ σ ∈ splittings X, ∃ g : σ.E ⟶ V, f = σ.πE ≫ g) :
    HSFormal.KaroubiFiltration 𝒰 where
  splittings := splittings
  mem := mem
  nonempty := nonempty
  directed := directed
  factor_to := factor_to
  factor_from := factor_from
  sum := by
    intro X Y b hb
    have htot := IsBilimit.binary_total hb
    have absR : ∀ {V Z : C}, 𝒰 V → ∀ f : V ⟶ Z, ∃ σ ∈ splittings Z, f ≫ σ.idem = f :=
      fun hV f ↦ by
        obtain ⟨σ, hσ, g, hg⟩ := factor_to hV f
        exact ⟨σ, hσ, absorbR_of_eq hg⟩
    have absL : ∀ {V Z : C}, 𝒰 V → ∀ f : Z ⟶ V, ∃ σ ∈ splittings Z, σ.idem ≫ f = f :=
      fun hV f ↦ by
        obtain ⟨σ, hσ, g, hg⟩ := factor_from hV f
        exact ⟨σ, hσ, absorbL_of_eq hg⟩
    constructor
    · intro σ hσ
      have hE := mem _ σ hσ
      obtain ⟨α, hα, hα₁, hα₂⟩ := exists_and_of_directed (directed X)
        (upClosed_absorbR (σ.ιE ≫ b.fst)) (upClosed_absorbL (b.inl ≫ σ.πE))
        (absR hE _) (absL hE _)
      obtain ⟨β, hβ, hβ₁, hβ₂⟩ := exists_and_of_directed (directed Y)
        (upClosed_absorbR (σ.ιE ≫ b.snd)) (upClosed_absorbL (b.inr ≫ σ.πE))
        (absR hE _) (absL hE _)
      refine ⟨α, hα, β, hβ, ?_, ?_⟩
      · have e₁ : σ.idem ≫ b.fst ≫ α.idem ≫ b.inl = σ.idem ≫ b.fst ≫ b.inl := by
          simp only [Splitting.idem, assoc] at hα₁ ⊢
          rw [reassoc_of% hα₁]
        have e₂ : σ.idem ≫ b.snd ≫ β.idem ≫ b.inr = σ.idem ≫ b.snd ≫ b.inr := by
          simp only [Splitting.idem, assoc] at hβ₁ ⊢
          rw [reassoc_of% hβ₁]
        rw [comp_add, e₁, e₂, ← comp_add, htot, comp_id]
      · have e₁ : (b.fst ≫ α.idem ≫ b.inl) ≫ σ.idem = b.fst ≫ b.inl ≫ σ.idem := by
          simp only [Splitting.idem, assoc] at hα₂ ⊢
          rw [reassoc_of% hα₂]
        have e₂ : (b.snd ≫ β.idem ≫ b.inr) ≫ σ.idem = b.snd ≫ b.inr ≫ σ.idem := by
          simp only [Splitting.idem, assoc] at hβ₂ ⊢
          rw [reassoc_of% hβ₂]
        rw [add_comp, e₁, e₂, ← assoc, ← assoc, ← add_comp, htot, id_comp]
    · intro α hα β hβ
      obtain ⟨σ₁, hσ₁, h₁, h₂⟩ := exists_and_of_directed (directed b.pt)
        (upClosed_absorbR (α.ιE ≫ b.inl)) (upClosed_absorbR (β.ιE ≫ b.inr))
        (absR (mem _ α hα) _) (absR (mem _ β hβ) _)
      obtain ⟨σ₂, hσ₂, h₃, h₄⟩ := exists_and_of_directed (directed b.pt)
        (upClosed_absorbL (b.fst ≫ α.πE)) (upClosed_absorbL (b.snd ≫ β.πE))
        (absL (mem _ α hα) _) (absL (mem _ β hβ) _)
      obtain ⟨σ, hσ, H₁, H₂⟩ := exists_and_of_directed (directed b.pt)
        (P := fun σ ↦ (α.ιE ≫ b.inl) ≫ σ.idem = α.ιE ≫ b.inl ∧
          (β.ιE ≫ b.inr) ≫ σ.idem = β.ιE ≫ b.inr)
        (Q := fun σ ↦ σ.idem ≫ b.fst ≫ α.πE = b.fst ≫ α.πE ∧
          σ.idem ≫ b.snd ≫ β.πE = b.snd ≫ β.πE)
        (fun σ ρ h hle ↦ ⟨upClosed_absorbR _ σ ρ h.1 hle, upClosed_absorbR _ σ ρ h.2 hle⟩)
        (fun σ ρ h hle ↦ ⟨upClosed_absorbL _ σ ρ h.1 hle, upClosed_absorbL _ σ ρ h.2 hle⟩)
        ⟨σ₁, hσ₁, h₁, h₂⟩ ⟨σ₂, hσ₂, h₃, h₄⟩
      refine ⟨σ, hσ, ?_, ?_⟩
      · simp only [Splitting.idem, assoc, add_comp] at H₁ ⊢
        rw [H₁.1, H₁.2]
      · simp only [Splitting.idem, assoc, comp_add] at H₂ ⊢
        rw [reassoc_of% H₂.1, reassoc_of% H₂.2]

end Generic

/-! ### Indexwise subcategories of `C_ℤ(A)` -/

section Retract

variable {V : Type*} [Category V] [Preadditive V] (P : ObjectProperty V)

omit [Preadditive V] in
/-- An object whose identity factors through `P` is a retract of a `P`-object. -/
lemma prop_of_factorsThrough_id [P.IsStableUnderRetracts] {X : V} (h : FactorsThrough P (𝟙 X)) :
    P X := by
  obtain ⟨W, hW, u, u', h⟩ := h
  exact P.prop_of_retract ⟨u, u', h.symm⟩ hW

variable {P} in
lemma factorsThrough_sum [HasBinaryBiproducts V] [IsAdditiveSub P] {X Y : V} {ι : Type*}
    (s : Finset ι) (f : ι → (X ⟶ Y)) (h : ∀ i ∈ s, FactorsThrough P (f i)) :
    FactorsThrough P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FactorsThrough.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end Retract

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- The subcategory of a Karoubi filtration is closed under retracts: a retract `X` of
`W ∈ U` is isomorphic to the summand `E_α` of `X` through which `W → X` factors. -/
instance isStableUnderRetracts : F.U.IsStableUnderRetracts where
  of_retract {X W} r hW := by
    obtain ⟨σ, hσ, g, hg⟩ := F.filt.factor_to hW r.r
    have h₁ : (r.i ≫ g) ≫ σ.ιE = 𝟙 X := by rw [assoc, ← hg, r.retract]
    have h₂ : σ.πE ≫ σ.ιE = 𝟙 X := by
      calc σ.πE ≫ σ.ιE = ((r.i ≫ g) ≫ σ.ιE) ≫ σ.πE ≫ σ.ιE := by rw [h₁, id_comp]
        _ = (r.i ≫ g) ≫ (σ.ιE ≫ σ.πE) ≫ σ.ιE := by simp only [assoc]
        _ = 𝟙 X := by rw [σ.ιE_πE, id_comp, h₁]
    exact F.U.prop_of_iso ⟨σ.ιE, σ.πE, σ.ιE_πE, h₂⟩ (F.filt.mem _ σ hσ)

end KaroubiFiltration

namespace CZ

variable {A : InvCat}

/-- The indexwise extension of a property of objects: all entries satisfy `P`. -/
def indexwise (P : ObjectProperty A) : ObjectProperty A.cz := fun X ↦ ∀ v, P (X.obj v)

lemma id_apply_self (X : A.cz) (v : ℤ) : (𝟙 X : X ⟶ X).1 v v = 𝟙 (X.obj v) :=
  diagMat_self (fun v ↦ 𝟙 (X.obj v)) v

lemma id_apply_ne (X : A.cz) {w v : ℤ} (h : v ≠ w) : (𝟙 X : X ⟶ X).1 w v = 0 :=
  diagMat_ne (fun v ↦ 𝟙 (X.obj v)) h

variable (P : ObjectProperty A) [IsAdditiveSub P]

/-- The entries of a composite through an object of `indexwise P` lie in `I_P`. -/
lemma factorsThrough_comp_apply {X Y Z : A.cz} (f : X ⟶ Y) (g : Y ⟶ Z) (hY : indexwise P Y)
    (u v : ℤ) : FactorsThrough P ((f ≫ g).1 u v) := by
  obtain ⟨b, hb⟩ := f.2
  rw [comp_apply_left f hb]
  exact factorsThrough_sum _ _ fun w _ ↦ FactorsThrough.of_mem (hY w) _ _

/-- The entries of a map in `I_{indexwise P}` lie in `I_P`. -/
lemma factorsThrough_apply {X Y : A.cz} {f : X ⟶ Y} (hf : FactorsThrough (indexwise P) f)
    (w v : ℤ) : FactorsThrough P (f.1 w v) := by
  obtain ⟨W, hW, u, u', rfl⟩ := hf
  exact factorsThrough_comp_apply P u u' hW w v

variable [P.IsStableUnderRetracts]

lemma indexwise_of_comp_eq_id {X Y : A.cz} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (hY : indexwise P Y) : indexwise P X := fun v ↦ prop_of_factorsThrough_id P <| by
  have := factorsThrough_comp_apply P f g hY v v
  rwa [h, id_apply_self] at this

instance indexwise_isStableUnderRetracts : (indexwise P).IsStableUnderRetracts where
  of_retract r hY := indexwise_of_comp_eq_id P r.i r.r r.retract hY

instance indexwise_isAdditiveSub : IsAdditiveSub (indexwise P) where
  of_iso e h := indexwise_of_comp_eq_id P e.inv e.hom e.inv_hom_id h
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨⟨fun _ ↦ Z⟩, isZero_of_forall fun _ ↦ hZ, fun _ ↦ hP⟩
  biprod_mem b hb hX hY v := prop_of_factorsThrough_id P <| by
    have := congrArg (fun φ ↦ φ.1 v v) (IsBilimit.binary_total hb)
    simp only [add_apply] at this
    rw [id_apply_self] at this
    rw [← this]
    exact (factorsThrough_comp_apply P _ _ hX v v).add (factorsThrough_comp_apply P _ _ hY v v)

/-! ### Indexwise splittings -/

/-- The indexwise (diagonal) splitting of `X : C_ℤ(A)` with components `σ v`. -/
@[simps]
def diagSplitting {X : A.cz} (σ : ∀ v, Splitting (X.obj v)) : Splitting X where
  E := ⟨fun v ↦ (σ v).E⟩
  U := ⟨fun v ↦ (σ v).U⟩
  ιE := diag fun v ↦ (σ v).ιE
  πE := diag fun v ↦ (σ v).πE
  ιU := diag fun v ↦ (σ v).ιU
  πU := diag fun v ↦ (σ v).πU
  ιE_πE := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (σ v).ιE_πE
  ιU_πU := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (σ v).ιU_πU
  ιE_πU := by rw [diag_comp_diag, ← diag_zero]; exact diag_ext fun v ↦ (σ v).ιE_πU
  ιU_πE := by rw [diag_comp_diag, ← diag_zero]; exact diag_ext fun v ↦ (σ v).ιU_πE
  total := by
    rw [diag_comp_diag, diag_comp_diag, ← diag_add, ← diag_id]
    exact diag_ext fun v ↦ (σ v).total

lemma diagSplitting_idem {X : A.cz} (σ : ∀ v, Splitting (X.obj v)) :
    (diagSplitting σ).idem = diag fun v ↦ (σ v).idem :=
  diag_comp_diag _ _

lemma idemLE_diag {X : A.cz} {d e : ∀ v, X.obj v ⟶ X.obj v} (h : ∀ v, IdemLE (d v) (e v)) :
    IdemLE (diag d) (diag e) :=
  ⟨by rw [diag_comp_diag]; exact diag_ext fun v ↦ (h v).1,
    by rw [diag_comp_diag]; exact diag_ext fun v ↦ (h v).2⟩

end CZ

namespace KaroubiFiltration

open CZ

variable {A B C : InvCat} (F : KaroubiFiltration A)

/-- **Rows.** A bounded matrix with entries in `I_U` is absorbed by one indexwise splitting of
its target: each row meets only a finite window. -/
lemma exists_row {X Y : A.cz} (f : X ⟶ Y) (h : ∀ w v, FactorsThrough F.U (f.1 w v)) :
    ∃ ρ : ∀ w, Splitting (Y.obj w), (∀ w, ρ w ∈ F.filt.splittings (Y.obj w)) ∧
      f ≫ (diagSplitting ρ).idem = f := by
  obtain ⟨b, hb⟩ := f.2
  have key : ∀ w, ∃ ρ ∈ F.filt.splittings (Y.obj w),
      ∀ v ∈ window w b, f.1 w v ≫ ρ.idem = f.1 w v := fun w ↦
    exists_forall_of_directed (F.filt.directed _) (F.filt.nonempty _) _
      (fun v ↦ upClosed_absorbR (f.1 w v)) fun v _ ↦ by
        obtain ⟨σ, hσ, g, hg⟩ := (F.factorsThrough_iff_target _).mp (h w v)
        exact ⟨σ, hσ, absorbR_of_eq hg⟩
  choose ρ hρ hρ' using key
  refine ⟨ρ, hρ, hom_ext fun w v ↦ ?_⟩
  rw [diagSplitting_idem, comp_diag_apply]
  by_cases hv : v ∈ window w b
  · exact hρ' w v hv
  · rw [hb.eq_zero_row hv, zero_comp]

/-- **Columns.** A bounded matrix with entries in `I_U` is absorbed by one indexwise splitting
of its source. -/
lemma exists_col {X Y : A.cz} (f : X ⟶ Y) (h : ∀ w v, FactorsThrough F.U (f.1 w v)) :
    ∃ ρ : ∀ v, Splitting (X.obj v), (∀ v, ρ v ∈ F.filt.splittings (X.obj v)) ∧
      (diagSplitting ρ).idem ≫ f = f := by
  obtain ⟨b, hb⟩ := f.2
  have key : ∀ v, ∃ ρ ∈ F.filt.splittings (X.obj v),
      ∀ w ∈ window v b, ρ.idem ≫ f.1 w v = f.1 w v := fun v ↦
    exists_forall_of_directed (F.filt.directed _) (F.filt.nonempty _) _
      (fun w ↦ upClosed_absorbL (f.1 w v)) fun w _ ↦ by
        obtain ⟨σ, hσ, g, hg⟩ := (F.factorsThrough_iff_source _).mp (h w v)
        exact ⟨σ, hσ, absorbL_of_eq hg⟩
  choose ρ hρ hρ' using key
  refine ⟨ρ, hρ, hom_ext fun w v ↦ ?_⟩
  rw [diagSplitting_idem, diag_comp_apply]
  by_cases hw : w ∈ window v b
  · exact hρ' v w hw
  · rw [hb.eq_zero_col hw, comp_zero]

/-- The indexwise splittings of `X : C_ℤ(A)`. -/
def czSplittings (X : A.cz) : Set (Splitting X) :=
  {τ | ∃ σ : ∀ v, Splitting (X.obj v), (∀ v, σ v ∈ F.filt.splittings (X.obj v)) ∧
    τ = diagSplitting σ}

lemma factorsThrough_apply_of_mem {X Y : A.cz} (hX : indexwise F.U X) (f : X ⟶ Y) (w v : ℤ) :
    FactorsThrough F.U (f.1 w v) := by
  simpa using FactorsThrough.of_mem (hX v) (𝟙 _) (f.1 w v)

lemma factorsThrough_apply_of_mem' {X Y : A.cz} (hY : indexwise F.U Y) (f : X ⟶ Y) (w v : ℤ) :
    FactorsThrough F.U (f.1 w v) := by
  simpa using FactorsThrough.of_mem (hY w) (f.1 w v) (𝟙 _)

/-- **[CP95, 1.27] for `C_ℤ`**: the Karoubi filtration `C_ℤ(U) ⊂ C_ℤ(A)` with indexwise
splittings. -/
def cz : KaroubiFiltration A.cz where
  U := indexwise F.U
  filt := HSFormal.KaroubiFiltration.ofFactor _ F.czSplittings
    (by
      rintro X _ ⟨σ, hσ, rfl⟩ v
      exact F.filt.mem _ _ (hσ v))
    (fun X ↦ ⟨_, fun v ↦ (F.filt.nonempty (X.obj v)).some,
      fun v ↦ (F.filt.nonempty (X.obj v)).some_mem, rfl⟩)
    (by
      rintro X _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
      choose ρ hρ h₁ h₂ using fun v ↦ F.filt.directed _ _ (hσ v) _ (hτ v)
      refine ⟨_, ⟨ρ, hρ, rfl⟩, ?_, ?_⟩ <;> rw [diagSplitting_idem, diagSplitting_idem]
      exacts [idemLE_diag h₁, idemLE_diag h₂])
    (by
      intro V X hV f
      obtain ⟨ρ, hρ, hf⟩ := F.exists_row f (F.factorsThrough_apply_of_mem hV f)
      exact ⟨_, ⟨ρ, hρ, rfl⟩, f ≫ (diagSplitting ρ).πE, by rw [assoc]; exact hf.symm⟩)
    (by
      intro X V hV f
      obtain ⟨ρ, hρ, hf⟩ := F.exists_col f (F.factorsThrough_apply_of_mem' hV f)
      exact ⟨_, ⟨ρ, hρ, rfl⟩, (diagSplitting ρ).ιE ≫ f, by rw [← assoc]; exact hf.symm⟩)
  star_ιE := by
    rintro X _ ⟨σ, hσ, rfl⟩
    exact (star_diag _).trans (diag_ext fun v ↦ F.star_ιE _ _ (hσ v))
  star_ιU := by
    rintro X _ ⟨σ, hσ, rfl⟩
    exact (star_diag _).trans (diag_ext fun v ↦ F.star_ιU _ _ (hσ v))

@[simp] lemma cz_U : F.cz.U = indexwise F.U := rfl

instance cz_isAdditiveSub : IsAdditiveSub F.cz.U := F.cz.additive

instance cz_isStableUnderRetracts : F.cz.U.IsStableUnderRetracts :=
  inferInstanceAs (indexwise F.U).IsStableUnderRetracts

lemma cz_splittings (X : A.cz) : F.cz.filt.splittings X = F.czSplittings X := rfl

/-- **The ideal `I_{C_ℤ(U)}`** consists of the bounded matrices with entries in `I_U`. -/
theorem factorsThrough_cz_iff {X Y : A.cz} (f : X ⟶ Y) :
    FactorsThrough F.cz.U f ↔ ∀ w v, FactorsThrough F.U (f.1 w v) := by
  refine ⟨fun h ↦ factorsThrough_apply F.U h, fun h ↦ ?_⟩
  obtain ⟨ρ, hρ, hf⟩ := F.exists_row f h
  rw [← hf]
  exact FactorsThrough.of_mem (W := (diagSplitting ρ).E) (fun w ↦ F.filt.mem _ _ (hρ w)) _ _
    |>.comp_left f

end KaroubiFiltration

/-! ### The subcategory: `C_ℤ(A) ⊇ indexwise P` is `C_ℤ(P)` -/

namespace CZ

variable {A : InvCat} (P : ObjectProperty A) [IsAdditiveSub P] [P.IsStableUnderRetracts]

omit [P.IsStableUnderRetracts] in
/-- `C_ℤ` of the inclusion is faithful. -/
lemma map_subIncl_injective {X Y : (A.sub P).cz} {f g : X ⟶ Y}
    (h : (map (A.subIncl P)).F.map f = (map (A.subIncl P)).F.map g) : f = g :=
  hom_ext fun w v ↦ ObjectProperty.hom_ext _ (congrArg (fun φ ↦ φ.1 w v) h)

omit [P.IsStableUnderRetracts] in
/-- A `C_ℤ(A)`-matrix between `P`-families as a `C_ℤ(P)`-matrix. -/
@[simps obj]
def subToFunctor : (indexwise P).FullSubcategory ⥤ Obj (A.sub P) where
  obj X := ⟨fun v ↦ ⟨X.obj.obj v, X.2 v⟩⟩
  map f := ⟨fun w v ↦ ObjectProperty.homMk (f.hom.1 w v),
    f.hom.2.elim fun b hb ↦ ⟨b, fun w v h ↦ ObjectProperty.hom_ext _ (hb w v h)⟩⟩
  map_id X := map_subIncl_injective P (by rw [CategoryTheory.Functor.map_id]; rfl)
  map_comp f g := map_subIncl_injective P (by rw [CategoryTheory.Functor.map_comp]; rfl)

omit [P.IsStableUnderRetracts] in
@[simp] lemma subToFunctor_map_apply {X Y : (indexwise P).FullSubcategory} (f : X ⟶ Y)
    (w v : ℤ) : ((subToFunctor P).map f).1 w v = ObjectProperty.homMk (f.hom.1 w v) := rfl

/-- **`C_ℤ(P)` is the subcategory of `P`-families of `C_ℤ(A)`** (strict `InvCat` iso). -/
def subIso : A.cz.sub (indexwise P) ≅ (A.sub P).cz where
  hom :=
    { F := subToFunctor P
      additive := ⟨hom_ext fun _ _ ↦ ObjectProperty.hom_ext _ rfl⟩
      map_star _ := hom_ext fun _ _ ↦ ObjectProperty.hom_ext _ rfl }
  inv :=
    { F := (indexwise P).lift (map (A.subIncl P)).F fun Y v ↦ (Y.obj v).2
      additive := ⟨ObjectProperty.hom_ext _ (map (A.subIncl P)).F.map_add⟩
      map_star f := ObjectProperty.hom_ext _ ((map (A.subIncl P)).map_star f) }
  hom_inv_id := rfl
  inv_hom_id := rfl

lemma subIso_hom_F : (subIso P).hom.F = subToFunctor P := rfl

/-- The iso is compatible with the inclusions. -/
@[simp] lemma subIso_hom_comp_map_subIncl :
    (subIso P).hom ≫ map (A.subIncl P) = A.cz.subIncl (indexwise P) := rfl

@[simp] lemma subIso_inv_comp_subIncl :
    (subIso P).inv ≫ A.cz.subIncl (indexwise P) = map (A.subIncl P) := rfl

end CZ

/-! ### The quotient: `C_ℤ(A)/C_ℤ(U) = C_ℤ(A/U)` -/

namespace KaroubiFiltration

open CZ

variable {A B C : InvCat} (F : KaroubiFiltration A)

/-- **`F.cz.sub ≅ F.sub.cz`** (strict). -/
abbrev czSubIso : F.cz.sub ≅ F.sub.cz := CZ.subIso F.U

lemma czSubIso_hom_comp_map_incl : F.czSubIso.hom ≫ CZ.map F.incl = F.cz.incl := rfl

lemma czSubIso_inv_comp_incl : F.czSubIso.inv ≫ F.cz.incl = CZ.map F.incl := rfl

/-- The comparison functor `C_ℤ(A)/C_ℤ(U) → C_ℤ(A/U)` induced by `C_ℤ` of the projection. -/
def czQuotHom : F.cz.quot ⟶ F.quot.cz where
  F := CategoryTheory.Quotient.lift (factorRel F.cz.U) (CZ.map F.proj).F
    fun _ _ f g (h : FactorsThrough F.cz.U (f - g)) ↦ hom_ext fun w v ↦
      (F.proj_map_eq_iff _ _).mpr (by simpa using (F.factorsThrough_cz_iff _).mp h w v)
  additive := ⟨by
    rintro _ _ ⟨f⟩ ⟨g⟩
    exact (CZ.map F.proj).F.map_add⟩
  map_star := by
    rintro _ _ ⟨f⟩
    exact (CZ.map F.proj).map_star f

@[simp] lemma czQuotHom_map_mk {X Y : A.cz} (f : X ⟶ Y) :
    F.czQuotHom.F.map ((CategoryTheory.Quotient.functor (factorRel F.cz.U)).map f) =
      (CZ.map F.proj).F.map f := rfl

/-- **Faithfulness**: a bounded matrix whose entries vanish in `A/U` factors through
`C_ℤ(U)`. -/
lemma czQuotHom_map_injective {X Y : F.cz.quot} {f g : X ⟶ Y}
    (h : F.czQuotHom.F.map f = F.czQuotHom.F.map g) : f = g := by
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  refine (quot_map_eq_iff f g).mpr ((F.factorsThrough_cz_iff _).mpr fun w v ↦ ?_)
  have := congrArg (fun φ ↦ φ.1 w v) h
  exact (F.proj_map_eq_iff _ _).mp this

open Classical in
/-- A representative of a class in `A/U`, chosen to be `0` on the zero class. -/
def quotRep {X Y : F.quot} (g : X ⟶ Y) : X.as ⟶ Y.as := if g = 0 then 0 else Quot.out g

lemma proj_map_quotRep {X Y : F.quot} (g : X ⟶ Y) : F.proj.F.map (F.quotRep g) = g := by
  unfold quotRep
  split_ifs with h
  · rw [h, Functor.map_zero] <;> rfl
  · exact Quot.out_eq g

/-- A bounded representative of a matrix over `A/U` (same propagation). -/
def czQuotRep {X Y : F.quot.cz} (g : X ⟶ Y) :
    (⟨fun v ↦ (X.obj v).as⟩ : A.cz) ⟶ ⟨fun v ↦ (Y.obj v).as⟩ :=
  ⟨fun w v ↦ F.quotRep (g.1 w v), g.2.elim fun b hb ↦ ⟨b, fun w v h ↦ by
    change F.quotRep (g.1 w v) = 0
    rw [quotRep, ite_eq_left (hb w v h)]⟩⟩

/-- The class of the bounded representative. -/
def czQuotLift {X Y : F.quot.cz} (g : X ⟶ Y) :
    (⟨⟨fun v ↦ (X.obj v).as⟩⟩ : F.cz.quot) ⟶ ⟨⟨fun v ↦ (Y.obj v).as⟩⟩ :=
  (CategoryTheory.Quotient.functor _).map (F.czQuotRep g)

lemma czQuotHom_map_lift {X Y : F.quot.cz} (g : X ⟶ Y) : F.czQuotHom.F.map (F.czQuotLift g) = g :=
  hom_ext fun w v ↦ F.proj_map_quotRep (g.1 w v)

/-- The inverse comparison functor: bounded representatives. -/
@[simps]
def czQuotInvFunctor : Obj F.quot ⥤ QuotCat F.cz.U where
  obj Y := ⟨⟨fun v ↦ (Y.obj v).as⟩⟩
  map g := F.czQuotLift g
  map_id Y := F.czQuotHom_map_injective (by
    erw [czQuotHom_map_lift, CategoryTheory.Functor.map_id]; rfl)
  map_comp f g := F.czQuotHom_map_injective (by
    erw [czQuotHom_map_lift, CategoryTheory.Functor.map_comp, czQuotHom_map_lift,
      czQuotHom_map_lift]; rfl)

/-- **`F.cz.quot ≅ F.quot.cz`**: the comparison functor is a strict `InvCat` isomorphism. -/
def czQuotIso : F.cz.quot ≅ F.quot.cz where
  hom := F.czQuotHom
  inv :=
    { F := F.czQuotInvFunctor
      additive := ⟨F.czQuotHom_map_injective (by
        erw [czQuotInvFunctor_map, czQuotHom_map_lift, CategoryTheory.Functor.map_add,
          czQuotInvFunctor_map, czQuotInvFunctor_map, czQuotHom_map_lift, czQuotHom_map_lift]; rfl)⟩
      map_star g := F.czQuotHom_map_injective (by
        erw [czQuotInvFunctor_map, czQuotHom_map_lift, F.czQuotHom.map_star,
          czQuotInvFunctor_map, czQuotHom_map_lift]; rfl) }
  hom_inv_id := InvCat.hom_ext <| CategoryTheory.Functor.ext (fun _ ↦ rfl) fun X Y f ↦ by
    erw [eqToHom_refl, eqToHom_refl, comp_id, id_comp]
    exact F.czQuotHom_map_injective (F.czQuotHom_map_lift _)
  inv_hom_id := InvCat.hom_ext <| CategoryTheory.Functor.ext (fun _ ↦ rfl) fun X Y g ↦ by
    erw [eqToHom_refl, eqToHom_refl, comp_id, id_comp]
    exact F.czQuotHom_map_lift g

lemma czQuotIso_hom : F.czQuotIso.hom = F.czQuotHom := rfl

/-- The iso is compatible with the projections. -/
lemma proj_comp_czQuotIso_hom : F.cz.proj ≫ F.czQuotIso.hom = CZ.map F.proj := rfl

end KaroubiFiltration

/-! ### Maps of filtrations and restriction -/

namespace FiltrationHom

variable {A B C : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
  {F'' : KaroubiFiltration C} (Φ : FiltrationHom F F')

/-- `C_ℤ` of a map of filtrations. -/
@[simps]
def cz : FiltrationHom F.cz F'.cz := ⟨CZ.map Φ.toHom, fun _ h v ↦ Φ.map_mem _ (h v)⟩

variable (F) in
@[simp] lemma cz_id : (FiltrationHom.id F).cz = FiltrationHom.id F.cz := rfl

@[simp] lemma cz_comp (Ψ : FiltrationHom F' F'') : (Φ.comp Ψ).cz = Φ.cz.comp Ψ.cz := rfl

/-- Compatibility with `czSubIso`: `Φ.cz.sub` is `C_ℤ(Φ.sub)`. -/
lemma cz_sub_comp_czSubIso : Φ.cz.sub ≫ F'.czSubIso.hom = F.czSubIso.hom ≫ CZ.map Φ.sub := rfl

/-- Compatibility with `czQuotIso`: `Φ.cz.quot` is `C_ℤ(Φ.quot)`. -/
lemma cz_quot_comp_czQuotIso :
    Φ.cz.quot ≫ F'.czQuotIso.hom = F.czQuotIso.hom ≫ CZ.map Φ.quot :=
  InvCat.hom_ext (CategoryTheory.Quotient.lift_unique' _ _ _ rfl)

end FiltrationHom

namespace KaroubiFiltration

open CZ

variable {A B : InvCat} (F : KaroubiFiltration A) (V : ObjectProperty A) [IsAdditiveSub V]
  [V.IsStableUnderRetracts]

/-- **Restriction commutes with `C_ℤ`**: `F.cz` restricted to `indexwise V` maps to
`(F.restrict V).cz` by the strict iso `CZ.subIso V` (inverse `czRestrictInv`). -/
def czRestrictHom : FiltrationHom (F.cz.restrict (indexwise V)) (F.restrict V).cz :=
  ⟨(CZ.subIso V).hom, fun _ h v ↦ h v⟩

/-- The inverse of `czRestrictHom`. -/
def czRestrictInv : FiltrationHom (F.restrict V).cz (F.cz.restrict (indexwise V)) :=
  ⟨(CZ.subIso V).inv, fun _ h v ↦ h v⟩

lemma czRestrictHom_comp_inv :
    (F.czRestrictHom V).comp (F.czRestrictInv V) = FiltrationHom.id _ := rfl

lemma czRestrictInv_comp_hom :
    (F.czRestrictInv V).comp (F.czRestrictHom V) = FiltrationHom.id _ := rfl

/-- Compatibility with the inclusions `restrictHom`. -/
lemma czRestrictHom_comp_restrictHom :
    (F.czRestrictHom V).comp (F.restrictHom V).cz = F.cz.restrictHom (indexwise V) := rfl

end KaroubiFiltration

/-! ### Iterates -/

namespace CZ

/-- `C_ℤ` of a strict isomorphism of `InvCat`s. -/
@[simps]
def mapIso {A B : InvCat} (e : A ≅ B) : A.cz ≅ B.cz where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end CZ

namespace KaroubiFiltration

variable {A B C : InvCat} (F : KaroubiFiltration A)

/-- The iterates `C_ℤ^{∘k}(U) ⊂ C_ℤ^{∘k}(A)`. -/
def czIter : ∀ k : ℕ, KaroubiFiltration (A.czIter k)
  | 0 => F
  | k + 1 => (czIter k).cz

@[simp] lemma czIter_zero : F.czIter 0 = F := rfl

@[simp] lemma czIter_succ (k : ℕ) : F.czIter (k + 1) = (F.czIter k).cz := rfl

/-- `(F.czIter k).sub ≅ C_ℤ^{∘k}(U)` (strict). -/
def czIterSubIso : ∀ k : ℕ, (F.czIter k).sub ≅ F.sub.czIter k
  | 0 => Iso.refl _
  | k + 1 => (F.czIter k).czSubIso ≪≫ CZ.mapIso (czIterSubIso k)

/-- `(F.czIter k).quot ≅ C_ℤ^{∘k}(A/U)` (strict). -/
def czIterQuotIso : ∀ k : ℕ, (F.czIter k).quot ≅ F.quot.czIter k
  | 0 => Iso.refl _
  | k + 1 => (F.czIter k).czQuotIso ≪≫ CZ.mapIso (czIterQuotIso k)

lemma czIterSubIso_hom_comp_mapIter_incl :
    ∀ k : ℕ, (F.czIterSubIso k).hom ≫ CZ.mapIter k F.incl = (F.czIter k).incl
  | 0 => Category.id_comp _
  | k + 1 => by
    change ((F.czIter k).czSubIso.hom ≫ CZ.map (F.czIterSubIso k).hom) ≫
      CZ.map (CZ.mapIter k F.incl) = _
    rw [assoc, ← CZ.map_comp, czIterSubIso_hom_comp_mapIter_incl k]
    rfl

lemma proj_comp_czIterQuotIso_hom :
    ∀ k : ℕ, (F.czIter k).proj ≫ (F.czIterQuotIso k).hom = CZ.mapIter k F.proj
  | 0 => Category.comp_id _
  | k + 1 => by
    change (F.czIter k).cz.proj ≫ (F.czIter k).czQuotIso.hom ≫ CZ.map (F.czIterQuotIso k).hom = _
    rw [← assoc, proj_comp_czQuotIso_hom, ← CZ.map_comp, proj_comp_czIterQuotIso_hom k]
    rfl

end KaroubiFiltration

namespace FiltrationHom

variable {A B C : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
  {F'' : KaroubiFiltration C} (Φ : FiltrationHom F F')

/-- The iterates `C_ℤ^{∘k}(Φ)`. -/
def czIter : ∀ k : ℕ, FiltrationHom (F.czIter k) (F'.czIter k)
  | 0 => Φ
  | k + 1 => (czIter k).cz

@[simp] lemma czIter_zero : Φ.czIter 0 = Φ := rfl

@[simp] lemma czIter_succ (k : ℕ) : Φ.czIter (k + 1) = (Φ.czIter k).cz := rfl

lemma czIter_toHom : ∀ k : ℕ, (Φ.czIter k).toHom = CZ.mapIter k Φ.toHom
  | 0 => rfl
  | k + 1 => congrArg CZ.map (czIter_toHom k)

variable (F) in
lemma czIter_id : ∀ k : ℕ, (FiltrationHom.id F).czIter k = FiltrationHom.id (F.czIter k)
  | 0 => rfl
  | k + 1 => by rw [czIter_succ, czIter_id k]; rfl

lemma czIter_comp (Ψ : FiltrationHom F' F'') :
    ∀ k : ℕ, (Φ.comp Ψ).czIter k = (Φ.czIter k).comp (Ψ.czIter k)
  | 0 => rfl
  | k + 1 => by rw [czIter_succ, czIter_comp Ψ k]; rfl

lemma czIter_sub_comp_czIterSubIso : ∀ k : ℕ,
    (Φ.czIter k).sub ≫ (F'.czIterSubIso k).hom = (F.czIterSubIso k).hom ≫ CZ.mapIter k Φ.sub
  | 0 => by simp [KaroubiFiltration.czIterSubIso, CZ.mapIter_zero]
  | k + 1 => by
    change (Φ.czIter k).cz.sub ≫ (F'.czIter k).czSubIso.hom ≫ CZ.map (F'.czIterSubIso k).hom =
      ((F.czIter k).czSubIso.hom ≫ CZ.map (F.czIterSubIso k).hom) ≫ CZ.map (CZ.mapIter k Φ.sub)
    rw [← assoc, cz_sub_comp_czSubIso, assoc, assoc, ← CZ.map_comp, ← CZ.map_comp,
      czIter_sub_comp_czIterSubIso k]

lemma czIter_quot_comp_czIterQuotIso : ∀ k : ℕ,
    (Φ.czIter k).quot ≫ (F'.czIterQuotIso k).hom = (F.czIterQuotIso k).hom ≫ CZ.mapIter k Φ.quot
  | 0 => by simp [KaroubiFiltration.czIterQuotIso, CZ.mapIter_zero]
  | k + 1 => by
    change (Φ.czIter k).cz.quot ≫ (F'.czIter k).czQuotIso.hom ≫ CZ.map (F'.czIterQuotIso k).hom =
      ((F.czIter k).czQuotIso.hom ≫ CZ.map (F.czIterQuotIso k).hom) ≫ CZ.map (CZ.mapIter k Φ.quot)
    rw [← assoc, cz_quot_comp_czQuotIso, assoc, assoc, ← CZ.map_comp, ← CZ.map_comp,
      czIter_quot_comp_czIterQuotIso k]

end FiltrationHom

end

end HSFormal.LTheory
