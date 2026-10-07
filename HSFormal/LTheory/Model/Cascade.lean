import HSFormal.LTheory.KaroubiFiltration

/-!
# Cascades of Karoubi splittings (lower L-theory model, module 12)

[CP95, 1.27] cascades for a `KaroubiFiltration F : U ⊂ A` (plan §3.2 (L1-ii), (L1-iv)).

* **Compression kills finite `I_U`-families.**  The splittings of `X` form a directed set; its
  filter of tails is `F.cofinal X`.  A map `f : W ⟶ X` lies in `I_U` iff eventually
  `f ≫ σ.πU = 0` (`factorsThrough_iff_eventually`), i.e. `f` factors through the `E_σ`-part;
  dually for maps out of `X` (`eventually_ιU_comp`).  Finitely many conditions hold for a
  single splitting (`exists_splitting_kill`).  For self-dual splittings the two are exchanged
  by the involution (`star_comp_πU`).
* **Downward cascades.**  For `d : X i ⟶ X (i-1)` vanishing above `top`, and conditions `P r`
  that hold eventually in each degree, `F.exists_cascade` chooses splittings `σ r` downward with
  `ιE_{r+1} ≫ d ≫ πU_r = 0` (the `E`-parts are closed under `d`) and `P r (σ r)`.
* **`E`-part subcomplexes.**  For an honest complex `D` this gives the subcomplex
  `Cascade.ePart` with objects in `U`, its inclusion, and the quotient `Cascade.uPart`
  (`= Compression.compressed`, `farClosed`); chain maps killed by the cascade factor through
  `ePart` (`Cascade.factor`).
* **Honest strict lifts.**  `SymLift F N`: objects of `A`, `d̃` with `d̃² ∈ I_U`, `φ̃` a chain
  map modulo `I_U`, `d̃` bounded.  A `SymLift.Cascade` (exists: `SymLift.nonempty_cascade`)
  kills `d̃²` and the chain defect of `φ̃`; then `C'' = (U_σ, ιU d̃ πU)` is an honest complex
  (`complex`), `φ'' = ιU φ̃ πU = π^* φ̃ π` an honest chain map (`sym`), strictly symmetric if `φ̃`
  is (`isStrictSymm_sym`, self-duality of the splittings), and `C''` is isomorphic in `A/U` to
  the quotient complex, carrying `φ''` to `[φ̃]` (`quotIso`, `quot_sym`).
  `exists_strictLift`: a bounded strictly symmetric complex in `A/U` is the image of an honest
  strictly symmetric complex in `A`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

/-! ### Splittings -/

namespace Casc

variable {C : Type*} [Category C] [Preadditive C] {X : C} (σ : Splitting X)

@[reassoc (attr := simp)]
lemma idem_idem : σ.idem ≫ σ.idem = σ.idem := by
  simp [Splitting.idem, reassoc_of% σ.ιE_πE]

lemma idemLE_refl : IdemLE σ.idem σ.idem := ⟨idem_idem σ, idem_idem σ⟩

omit [Preadditive C] in
lemma idemLE_trans {e e' e'' : X ⟶ X} (h : IdemLE e e') (h' : IdemLE e' e'') : IdemLE e e'' :=
  ⟨by rw [← h.1, assoc, h'.1], by rw [← h.2, ← assoc, h'.2]⟩

@[reassoc (attr := simp)]
lemma ιE_idem : σ.ιE ≫ σ.idem = σ.ιE := by simp [Splitting.idem, reassoc_of% σ.ιE_πE]

@[reassoc (attr := simp)]
lemma idem_πE : σ.idem ≫ σ.πE = σ.πE := by simp [Splitting.idem, σ.ιE_πE]

@[reassoc (attr := simp)]
lemma idem_πU : σ.idem ≫ σ.πU = 0 := by simp [Splitting.idem, σ.ιE_πU]

@[reassoc (attr := simp)]
lemma ιU_idem : σ.ιU ≫ σ.idem = 0 := by simp [Splitting.idem, reassoc_of% σ.ιU_πE]

@[reassoc]
lemma πU_ιU : σ.πU ≫ σ.ιU = 𝟙 X - σ.idem := by
  rw [← σ.total, Splitting.idem]; abel

/-- `f` is killed by compression to `U_σ` iff it factors through `E_σ`. -/
lemma comp_πU_eq_zero_iff {W : C} (f : W ⟶ X) :
    f ≫ σ.πU = 0 ↔ f = (f ≫ σ.πE) ≫ σ.ιE := by
  constructor
  · intro h
    conv_lhs => rw [← comp_id f, ← σ.total]
    simp [reassoc_of% h]
  · intro h; rw [h]; simp [σ.ιE_πU]

lemma comp_πU_eq_zero_iff_idem {W : C} (f : W ⟶ X) : f ≫ σ.πU = 0 ↔ f ≫ σ.idem = f := by
  rw [comp_πU_eq_zero_iff, Splitting.idem, assoc, eq_comm]

/-- `g` is killed by restriction to `U_σ` iff it factors through `E_σ`. -/
lemma ιU_comp_eq_zero_iff {W : C} (g : X ⟶ W) :
    σ.ιU ≫ g = 0 ↔ g = σ.πE ≫ σ.ιE ≫ g := by
  constructor
  · intro h
    conv_lhs => rw [← id_comp g, ← σ.total]
    simp [h]
  · intro h; rw [h, reassoc_of% σ.ιU_πE, zero_comp]

lemma ιU_comp_eq_zero_iff_idem {W : C} (g : X ⟶ W) : σ.ιU ≫ g = 0 ↔ σ.idem ≫ g = g := by
  rw [ιU_comp_eq_zero_iff, Splitting.idem, assoc, eq_comm]

variable {σ} {τ : Splitting X}

/-- `E_σ ⊆ E_τ`. -/
@[reassoc]
lemma ιE_πU_of_le (h : IdemLE σ.idem τ.idem) : σ.ιE ≫ τ.πU = 0 := by
  rw [← ιE_idem σ, assoc, ← h.1, assoc, idem_πU, comp_zero, comp_zero]

/-- `U_τ ⊆ U_σ`. -/
@[reassoc]
lemma ιU_πE_of_le (h : IdemLE σ.idem τ.idem) : τ.ιU ≫ σ.πE = 0 := by
  rw [← idem_πE σ, ← h.2, assoc, reassoc_of% (ιU_idem τ), zero_comp]

end Casc

/-! ### The cofinal filter of splittings -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- The filter of tails `{σ | σ₀ ≤ σ}` of the directed set of splittings of `X` (axiom (i)). -/
def cofinal (X : A) : Filter (Splitting X) where
  sets := {S | ∃ σ₀ ∈ F.filt.splittings X, ∀ σ ∈ F.filt.splittings X, IdemLE σ₀.idem σ.idem → σ ∈ S}
  univ_sets := let ⟨σ₀, h⟩ := F.filt.nonempty X; ⟨σ₀, h, fun _ _ _ ↦ trivial⟩
  sets_of_superset := fun ⟨σ₀, h, H⟩ hST ↦ ⟨σ₀, h, fun σ hσ hle ↦ hST (H σ hσ hle)⟩
  inter_sets := fun ⟨σ₀, h₀, H₀⟩ ⟨σ₁, h₁, H₁⟩ ↦ by
    obtain ⟨ρ, hρ, h0, h1⟩ := F.filt.directed _ σ₀ h₀ σ₁ h₁
    exact ⟨ρ, hρ, fun σ hσ hle ↦
      ⟨H₀ σ hσ (Casc.idemLE_trans h0 hle), H₁ σ hσ (Casc.idemLE_trans h1 hle)⟩⟩

variable {F} {X W : A}

lemma mem_cofinal {S : Set (Splitting X)} : S ∈ F.cofinal X ↔
    ∃ σ₀ ∈ F.filt.splittings X, ∀ σ ∈ F.filt.splittings X, IdemLE σ₀.idem σ.idem → σ ∈ S :=
  Iff.rfl

instance (X : A) : (F.cofinal X).NeBot :=
  Filter.forall_mem_nonempty_iff_neBot.mp fun _ ⟨σ₀, h, H⟩ ↦ ⟨σ₀, H σ₀ h (Casc.idemLE_refl σ₀)⟩

variable (F) in
lemma eventually_mem (X : A) : ∀ᶠ σ in F.cofinal X, σ ∈ F.filt.splittings X :=
  let ⟨σ₀, h⟩ := F.filt.nonempty X; ⟨σ₀, h, fun _ hσ _ ↦ hσ⟩

lemma eventually_idemLE {σ₀ : Splitting X} (h : σ₀ ∈ F.filt.splittings X) :
    ∀ᶠ σ in F.cofinal X, IdemLE σ₀.idem σ.idem :=
  ⟨σ₀, h, fun _ _ hle ↦ hle⟩

/-- **Compression kills `I_U`** (target side): eventually `f ≫ πU = 0`. -/
lemma eventually_comp_πU {f : W ⟶ X} (hf : FactorsThrough F.U f) :
    ∀ᶠ σ in F.cofinal X, f ≫ σ.πU = 0 := by
  obtain ⟨σ₀, hσ₀, g, rfl⟩ := (F.factorsThrough_iff_target f).mp hf
  exact ⟨σ₀, hσ₀, fun σ _ hle ↦ by simp [Casc.ιE_πU_of_le hle]⟩

/-- **Compression kills `I_U`** (source side): eventually `ιU ≫ g = 0`. -/
lemma eventually_ιU_comp {g : X ⟶ W} (hg : FactorsThrough F.U g) :
    ∀ᶠ σ in F.cofinal X, σ.ιU ≫ g = 0 := by
  obtain ⟨σ₀, hσ₀, g, rfl⟩ := (F.factorsThrough_iff_source g).mp hg
  exact ⟨σ₀, hσ₀, fun σ _ hle ↦ by simp [Casc.ιU_πE_of_le_assoc hle]⟩

lemma eventually_comp_idem {f : W ⟶ X} (hf : FactorsThrough F.U f) :
    ∀ᶠ σ in F.cofinal X, f ≫ σ.idem = f :=
  (eventually_comp_πU hf).mono fun σ h ↦ (Casc.comp_πU_eq_zero_iff_idem σ f).mp h

lemma eventually_idem_comp {g : X ⟶ W} (hg : FactorsThrough F.U g) :
    ∀ᶠ σ in F.cofinal X, σ.idem ≫ g = g :=
  (eventually_ιU_comp hg).mono fun σ h ↦ (Casc.ιU_comp_eq_zero_iff_idem σ g).mp h

lemma factorsThrough_of_comp_πU {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) {f : W ⟶ X}
    (h : f ≫ σ.πU = 0) : FactorsThrough F.U f := by
  rw [(Casc.comp_πU_eq_zero_iff σ f).mp h]
  exact FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _

lemma factorsThrough_of_ιU_comp {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) {g : X ⟶ W}
    (h : σ.ιU ≫ g = 0) : FactorsThrough F.U g := by
  rw [(Casc.ιU_comp_eq_zero_iff σ g).mp h]
  exact FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _

lemma factorsThrough_ιE_comp {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) (g : X ⟶ W) :
    FactorsThrough F.U (σ.ιE ≫ g) := by
  rw [← id_comp (σ.ιE ≫ g)]
  exact FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _

lemma factorsThrough_comp_πE {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) (f : W ⟶ X) :
    FactorsThrough F.U (f ≫ σ.πE) := by
  rw [← comp_id (f ≫ σ.πE)]
  exact FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _

/-- `I_U` is exactly the set of maps killed by eventually all compressions. -/
theorem factorsThrough_iff_eventually (f : W ⟶ X) :
    FactorsThrough F.U f ↔ ∀ᶠ σ in F.cofinal X, f ≫ σ.πU = 0 := by
  refine ⟨eventually_comp_πU, fun h ↦ ?_⟩
  obtain ⟨σ, h, hσ⟩ := (h.and (F.eventually_mem X)).exists
  exact factorsThrough_of_comp_πU hσ h

theorem factorsThrough_iff_eventually' (g : X ⟶ W) :
    FactorsThrough F.U g ↔ ∀ᶠ σ in F.cofinal X, σ.ιU ≫ g = 0 := by
  refine ⟨eventually_ιU_comp, fun h ↦ ?_⟩
  obtain ⟨σ, h, hσ⟩ := (h.and (F.eventually_mem X)).exists
  exact factorsThrough_of_ιU_comp hσ h

/-- **[CP95, 1.27] for finite families.**  Finitely many `I_U`-maps into and out of `X` all
factor through the `E`-part of a single splitting `σ`, i.e. compression to `U_σ` kills them. -/
theorem exists_splitting_kill {ι κ : Type*} [Finite ι] [Finite κ] {V : ι → A} {V' : κ → A}
    (f : ∀ i, V i ⟶ X) (g : ∀ k, X ⟶ V' k) (hf : ∀ i, FactorsThrough F.U (f i))
    (hg : ∀ k, FactorsThrough F.U (g k)) :
    ∃ σ ∈ F.filt.splittings X, (∀ i, f i ≫ σ.πU = 0) ∧ (∀ k, σ.ιU ≫ g k = 0) := by
  obtain ⟨σ, hσ, h₁, h₂⟩ := ((F.eventually_mem X).and ((Filter.eventually_all.mpr fun i ↦
    eventually_comp_πU (hf i)).and (Filter.eventually_all.mpr fun k ↦
      eventually_ιU_comp (hg k)))).exists
  exact ⟨σ, hσ, h₁, h₂⟩

/-- Self-duality exchanges the two kinds of compression: `(f πU)^* = ιU f^*`. -/
lemma star_comp_πU {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) (f : W ⟶ X) :
    A.inv.star (f ≫ σ.πU) = σ.ιU ≫ A.inv.star f := by
  rw [A.inv.star_comp, star_πU hσ]

lemma star_ιU_comp {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) (g : X ⟶ W) :
    A.inv.star (σ.ιU ≫ g) = A.inv.star g ≫ σ.πU := by
  rw [A.inv.star_comp, F.star_ιU X σ hσ]

lemma star_ιE_comp {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) (g : X ⟶ W) :
    A.inv.star (σ.ιE ≫ g) = A.inv.star g ≫ σ.πE := by
  rw [A.inv.star_comp, F.star_ιE X σ hσ]

/-- In `A/U`, `[πU] [ιU] = 1`: compression to `U_σ` is an isomorphism modulo `I_U`. -/
@[reassoc]
lemma proj_map_πU_ιU {σ : Splitting X} (hσ : σ ∈ F.filt.splittings X) :
    F.proj.F.map σ.πU ≫ F.proj.F.map σ.ιU = 𝟙 _ := by
  rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id, F.proj_map_eq_iff, Casc.πU_ιU,
    sub_sub_cancel_left, Splitting.idem]
  exact (FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _).neg

lemma proj_map_ιU_πU (σ : Splitting X) : F.proj.F.map σ.ιU ≫ F.proj.F.map σ.πU = 𝟙 _ := by
  rw [← Functor.map_comp, σ.ιU_πU, CategoryTheory.Functor.map_id]

end KaroubiFiltration

/-! ### Downward cascades -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

open Classical in
/-- A splitting in the family of `Y` satisfying `Q`, if there is one. -/
def chooseSplitting {Y : A} (Q : Splitting Y → Prop) : Splitting Y :=
  if h : ∃ σ ∈ F.filt.splittings Y, Q σ then h.choose else (F.filt.nonempty Y).some

lemma chooseSplitting_mem {Y : A} (Q : Splitting Y → Prop) :
    F.chooseSplitting Q ∈ F.filt.splittings Y := by
  unfold chooseSplitting
  split_ifs with h
  · exact h.choose_spec.1
  · exact (F.filt.nonempty Y).some_mem

lemma chooseSplitting_spec {Y : A} {Q : Splitting Y → Prop} (hQ : ∀ᶠ σ in F.cofinal Y, Q σ) :
    Q (F.chooseSplitting Q) := by
  have h : ∃ σ ∈ F.filt.splittings Y, Q σ := by
    obtain ⟨σ, h₁, h₂⟩ := ((F.eventually_mem Y).and hQ).exists
    exact ⟨σ, h₁, h₂⟩
  unfold chooseSplitting
  rw [dif_pos h]
  exact h.choose_spec.2

variable {X : ℤ → A} (d : ∀ i j, X i ⟶ X j) (top : ℤ) (P : ∀ r, Splitting (X r) → Prop)

/-- The downward cascade: `σ r` satisfies `P r`, and for `r < top` it absorbs `d(E_{r+1})`. -/
def cascade (r : ℤ) : Splitting (X r) :=
  if top ≤ r then F.chooseSplitting (P r)
  else F.chooseSplitting fun τ ↦ P r τ ∧ (cascade (r + 1)).ιE ≫ d (r + 1) r ≫ τ.πU = 0
termination_by (top - r).toNat
decreasing_by omega

/-- Splittings `X r = E_r ⊕ U_r` from the families of `F` whose `E`-parts are closed under `d`:
`ιE ≫ d ≫ πU = 0` (the plan's `π_{r-1} d̃ ιE_r = 0`). -/
structure Cascade where
  σ : ∀ r, Splitting (X r)
  mem : ∀ r, σ r ∈ F.filt.splittings (X r)
  ιE_d_πU : ∀ i j, (σ i).ιE ≫ d i j ≫ (σ j).πU = 0

/-- **Downward cascade.**  If `d` has degree `-1` and vanishes above `top`, then for conditions
`P r` holding eventually in each degree there are splittings `σ r ⊨ P r` whose `E`-parts are
closed under `d`. -/
theorem exists_cascade (hshape : ∀ i j, ¬ (ComplexShape.down ℤ).Rel i j → d i j = 0)
    (htop : ∀ i j, top < i → d i j = 0) (hP : ∀ r, ∀ᶠ σ in F.cofinal (X r), P r σ) :
    ∃ c : F.Cascade d, ∀ r, P r (c.σ r) := by
  have mem : ∀ r, F.cascade d top P r ∈ F.filt.splittings (X r) := fun r ↦ by
    rw [cascade]; split_ifs <;> exact F.chooseSplitting_mem _
  have key : ∀ r, P r (F.cascade d top P r) ∧
      (F.cascade d top P (r + 1)).ιE ≫ d (r + 1) r ≫ (F.cascade d top P r).πU = 0 := fun r ↦ by
    by_cases h : top ≤ r
    · refine ⟨?_, by rw [htop _ _ (by omega)]; simp⟩
      rw [cascade, if_pos h]
      exact F.chooseSplitting_spec (hP r)
    · rw [cascade, if_neg h]
      exact F.chooseSplitting_spec ((hP r).and ((eventually_comp_πU
        (factorsThrough_ιE_comp (mem (r + 1)) (d (r + 1) r))).mono fun τ h ↦ by rwa [assoc] at h))
  refine ⟨⟨F.cascade d top P, mem, fun i j ↦ ?_⟩, fun r ↦ (key r).1⟩
  by_cases hij : i = j + 1
  · subst hij; exact (key j).2
  · rw [hshape i j (by simp; omega)]; simp

namespace Cascade

variable {F} {d} (c : F.Cascade d)

/-- The `E`-parts are closed under `d`: `ιE d = (ιE d πE) ιE`. -/
@[reassoc]
lemma ιE_d_πE_ιE (i j : ℤ) :
    (c.σ i).ιE ≫ d i j ≫ (c.σ j).πE ≫ (c.σ j).ιE = (c.σ i).ιE ≫ d i j := by
  have := (Casc.comp_πU_eq_zero_iff_idem (c.σ j) ((c.σ i).ιE ≫ d i j)).mp
    (by rw [assoc]; exact c.ιE_d_πU i j)
  simpa [Splitting.idem] using this

/-- Dually, `πU d = πU (ιU d πU)` on the `U`-parts. -/
@[reassoc]
lemma πU_ιU_d_πU (i j : ℤ) :
    (c.σ i).πU ≫ (c.σ i).ιU ≫ d i j ≫ (c.σ j).πU = d i j ≫ (c.σ j).πU := by
  rw [Casc.πU_ιU_assoc, sub_comp, id_comp, Splitting.idem, assoc, c.ιE_d_πU, comp_zero,
    sub_zero]

/-- The dual statement, using self-duality of the splittings. -/
@[reassoc]
lemma ιU_star_d_πU_ιU (i j : ℤ) :
    (c.σ j).ιU ≫ A.inv.star (d i j) ≫ (c.σ i).πU ≫ (c.σ i).ιU =
      (c.σ j).ιU ≫ A.inv.star (d i j) := by
  have := congrArg A.inv.star (c.πU_ιU_d_πU i j)
  simpa only [A.inv.star_comp, star_πU (c.mem _), F.star_ιU _ _ (c.mem _), assoc] using this

/-- The `U`-part complex `(U_σ, ιU d πU)`, given that the cascade kills `d²`. -/
@[simps, reducible]
def uComplex (hshape : ∀ i j, ¬ (ComplexShape.down ℤ).Rel i j → d i j = 0)
    (hdd : ∀ i j k, d i j ≫ d j k ≫ (c.σ k).πU = 0) : ChainComplex A ℤ where
  X r := (c.σ r).U
  d i j := (c.σ i).ιU ≫ d i j ≫ (c.σ j).πU
  shape i j h := by rw [hshape i j h]; simp
  d_comp_d' i j k _ _ := by
    simp only [assoc]
    rw [c.πU_ιU_d_πU j k, hdd, comp_zero]

end Cascade

end KaroubiFiltration

/-! ### `E`-part subcomplexes of honest complexes -/

namespace KaroubiFiltration

namespace Cascade

variable {A : InvCat} {F : KaroubiFiltration A} {D : ChainComplex A ℤ} (c : F.Cascade D.d)

/-- The `E`-part subcomplex `K ⊂ D`; its objects lie in `U` (`ePart_mem`). -/
@[simps, reducible]
def ePart : ChainComplex A ℤ where
  X r := (c.σ r).E
  d i j := (c.σ i).ιE ≫ D.d i j ≫ (c.σ j).πE
  shape i j h := by rw [D.shape i j h]; simp
  d_comp_d' i j k _ _ := by simp only [assoc]; rw [c.ιE_d_πE_ιE_assoc]; simp

lemma ePart_mem (r : ℤ) : F.U (c.ePart.X r) := F.filt.mem _ _ (c.mem r)

/-- The inclusion `K ⟶ D`. -/
@[simps]
def ι : c.ePart ⟶ D where
  f r := (c.σ r).ιE
  comm' i j _ := by simp only [ePart_d, assoc]; rw [c.ιE_d_πE_ιE]

/-- The quotient `D/K = (U_σ, ιU d πU)`. -/
abbrev uPart : ChainComplex A ℤ := c.uComplex D.shape fun i j k ↦ by simp

/-- The projection `D ⟶ D/K`. -/
@[simps]
def π : D ⟶ c.uPart where
  f r := (c.σ r).πU
  comm' i j _ := by simp only [uComplex_d]; rw [c.πU_ιU_d_πU]

@[reassoc (attr := simp)]
lemma ι_π : c.ι ≫ c.π = 0 := by ext r; simp [(c.σ r).ιE_πU]

/-- A chain map killed by the compressions `πU` factors through the `E`-part subcomplex. -/
@[simps]
def factor {W : ChainComplex A ℤ} (e : W ⟶ D) (he : ∀ r, e.f r ≫ (c.σ r).πU = 0) :
    W ⟶ c.ePart where
  f r := e.f r ≫ (c.σ r).πE
  comm' i j _ := by
    have h : e.f i ≫ (c.σ i).πE ≫ (c.σ i).ιE = e.f i := by
      rw [← assoc]; exact ((Casc.comp_πU_eq_zero_iff _ _).mp (he i)).symm
    simp only [ePart_d, assoc]
    rw [reassoc_of% h, e.comm_assoc]

@[reassoc (attr := simp)]
lemma factor_ι {W : ChainComplex A ℤ} (e : W ⟶ D) (he : ∀ r, e.f r ≫ (c.σ r).πU = 0) :
    c.factor e he ≫ c.ι = e := by
  ext r
  simpa using ((Casc.comp_πU_eq_zero_iff _ _).mp (he r)).symm

/-- The `U`-parts as a near part of `D` in the sense of `Compression` (§9). -/
def toNearPart : NearPart (fun r ↦ (c.σ r).U) D :=
  fun r ↦ ⟨(c.σ r).ιU, (c.σ r).πU, (c.σ r).ιU_πU⟩

lemma far_toNearPart (r : ℤ) : far (c.toNearPart r) = (c.σ r).idem := by
  simp [far, toNearPart, Casc.πU_ιU]

/-- The far (`E`-) parts form a subcomplex. -/
theorem farClosed : FarClosed c.toNearPart := fun i j ↦ by
  rw [far_toNearPart, Splitting.idem]
  simp [toNearPart, c.ιE_d_πU]

theorem compressed_eq : compressed c.toNearPart (.inl c.farClosed) = c.uPart := rfl

end Cascade

variable {A : InvCat} (F : KaroubiFiltration A)

/-- **Absorbing an `I_U` chain map** (input of plan (L1-iv)): for `D` bounded above and a chain
map `e` with components in `I_U` there is a cascade whose `E`-part subcomplex (objects in `U`)
absorbs `e`, i.e. `e` factors through `ePart` (`Cascade.factor`). -/
theorem exists_cascade_absorb {D W : ChainComplex A ℤ} (top : ℤ)
    (htop : ∀ i j, top < i → D.d i j = 0) (e : W ⟶ D) (he : ∀ r, FactorsThrough F.U (e.f r)) :
    ∃ c : F.Cascade D.d, ∀ r, e.f r ≫ (c.σ r).πU = 0 :=
  F.exists_cascade D.d top _ D.shape htop fun r ↦ eventually_comp_πU (he r)

end KaroubiFiltration

/-! ### Honest strict lifts (plan (L1-ii)) -/

namespace Casc

lemma map_units_smul {V W : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
    (Φ : V ⥤ W) [Φ.Additive] {X Y : V} (u : ℤˣ) (f : X ⟶ Y) : Φ.map (u • f) = u • Φ.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

lemma comp_eqToHom_fam {V : Type*} [Category V] {X Y : ℤ → V} (g : ∀ k, X k ⟶ Y k) {a b : ℤ}
    (h : a = b) : g a ≫ eqToHom (congrArg Y h) = eqToHom (congrArg X h) ≫ g b := by
  subst h; simp

end Casc

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) (N : ℤ)

/-- Input of plan (L1-ii): a symmetric complex of `A/U` lifted to `A` modulo `I_U`.  Objects of
`A`, `d̃` of degree `-1` with `d̃² ∈ I_U`, vanishing above `top`, and `φ̃_r : X_{N-r} ⟶ X_r` a
chain map `X^{N-*} ⟶ X` modulo `I_U`, for Ranicki's dual differential `(-1)^r d̃^*_{N-r+1}`. -/
structure SymLift where
  X : ℤ → A
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬ (ComplexShape.down ℤ).Rel i j → d i j = 0
  d_comp_d : ∀ i j k, FactorsThrough F.U (d i j ≫ d j k)
  top : ℤ
  d_eq_zero : ∀ i j, top < i → d i j = 0
  φ : ∀ r, X (N - r) ⟶ X r
  comm : ∀ r r', FactorsThrough F.U
    (φ r ≫ d r r' - (r.negOnePow • A.inv.star (d (N - r') (N - r))) ≫ φ r')

namespace SymLift

variable {F N} (L : F.SymLift N)

/-- The dual differential `δ_{r,r'} = (-1)^r d̃^*_{N-r',N-r}`. -/
def dualD (r r' : ℤ) : L.X (N - r) ⟶ L.X (N - r') :=
  r.negOnePow • A.inv.star (L.d (N - r') (N - r))

/-- A (self-dual) cascade adapted to `L`: `E`-parts closed under `d̃`, and the compressions
`πU` kill `d̃²` and the chain defect of `φ̃`. -/
structure Cascade extends F.Cascade L.d where
  dd : ∀ i j k, L.d i j ≫ L.d j k ≫ (σ k).πU = 0
  comm : ∀ r r', (L.φ r ≫ L.d r r' - L.dualD r r' ≫ L.φ r') ≫ (σ r').πU = 0

/-- **Self-dual cascade** (plan (L1-ii)): downward choice of splittings `σ_{r}` from `σ_{r+1}`. -/
theorem nonempty_cascade : Nonempty L.Cascade := by
  obtain ⟨c, hc⟩ := F.exists_cascade L.d L.top
    (fun r τ ↦ L.d (r + 1 + 1) (r + 1) ≫ L.d (r + 1) r ≫ τ.πU = 0 ∧
      (L.φ (r + 1) ≫ L.d (r + 1) r - L.dualD (r + 1) r ≫ L.φ r) ≫ τ.πU = 0)
    L.shape L.d_eq_zero fun r ↦
      ((eventually_comp_πU (L.d_comp_d _ _ _)).mono fun τ h ↦ by rwa [assoc] at h).and
        (eventually_comp_πU (L.comm _ _))
  refine ⟨⟨c, fun i j k ↦ ?_, fun r r' ↦ ?_⟩⟩
  · by_cases hjk : j = k + 1
    · by_cases hij : i = j + 1
      · subst hjk hij; exact (hc k).1
      · rw [L.shape i j (by simp; omega)]; simp
    · rw [L.shape j k (by simp; omega)]; simp
  · by_cases h : r = r' + 1
    · subst h; exact (hc r').2
    · rw [L.shape r r' (by simp; omega), dualD, L.shape (N - r') (N - r) (by simp; omega)]; simp

/-- A chosen adapted cascade. -/
def cascade : L.Cascade := Classical.choice L.nonempty_cascade

/-- The complex of `A/U` represented by `L`. -/
@[simps, reducible]
def quotComplex : ChainComplex F.quot ℤ where
  X r := F.proj.F.obj (L.X r)
  d i j := F.proj.F.map (L.d i j)
  shape i j h := by rw [L.shape i j h, Functor.map_zero]
  d_comp_d' i j k _ _ := by
    rw [← Functor.map_comp, ← Functor.map_zero F.proj.F (L.X i) (L.X k), F.proj_map_eq_iff,
      sub_zero]
    exact L.d_comp_d i j k

/-- The chain map `[φ̃] : C^{N-*} ⟶ C` of `A/U`. -/
@[simps]
def quotSym : dualComplex F.quot.inv N L.quotComplex ⟶ L.quotComplex where
  f r := F.proj.F.map (L.φ r)
  comm' r r' _ := by
    simp only [quotComplex_d, dualComplex_d, quotComplex_X, ← F.proj.map_star,
      ← Casc.map_units_smul, ← Functor.map_comp]
    exact (F.proj_map_eq_iff _ _).mpr (L.comm r r')

namespace Cascade

variable {L} (c : L.Cascade)

/-- The honest lift `C'' = (U_σ, ιU d̃ πU)` in `A`. -/
abbrev complex : ChainComplex A ℤ := c.toCascade.uComplex L.shape c.dd

lemma complex_d_eq_zero {i j : ℤ} (h : L.d i j = 0) : c.complex.d i j = 0 := by
  simp [h]

/-- `φ'' = ιU φ̃ πU = π^* φ̃ π`: an honest chain map `C''^{N-*} ⟶ C''`.  The cross terms vanish
by `E`-closedness and its dual, which uses the self-duality of the splittings. -/
@[simps]
def sym : dualComplex A.inv N c.complex ⟶ c.complex where
  f r := (c.σ (N - r)).ιU ≫ L.φ r ≫ (c.σ r).πU
  comm' r r' _ := by
    have h := c.comm r r'
    rw [sub_comp, sub_eq_zero, assoc, assoc, dualD, Linear.units_smul_comp] at h
    simp only [dualComplex_d, Cascade.uComplex_d, A.inv.star_comp, star_πU (c.mem _),
      F.star_ιU _ _ (c.mem _), assoc, Linear.units_smul_comp]
    rw [c.toCascade.πU_ιU_d_πU r r', c.toCascade.ιU_star_d_πU_ιU_assoc, h,
      Linear.comp_units_smul]

/-- **Self-duality**: if `φ̃` is strictly symmetric (`Tφ̃ = φ̃`), so is `φ''`. -/
theorem isStrictSymm_sym (hφ : ∀ r, L.φ r = transposeFamily A.inv N L.X L.φ r) :
    IsStrictSymm A.inv N c.sym := by
  ext r
  rw [transposeHom_f, sym_f, sym_f]
  simp only [A.inv.star_comp, star_πU (c.mem _), F.star_ιU _ _ (c.mem _), assoc]
  rw [Casc.comp_eqToHom_fam (Y := c.complex.X) (fun k ↦ (c.σ k).πU) (sub_sub_cancel N r),
    hφ r, transposeFamily]
  simp [Linear.comp_units_smul, Linear.units_smul_comp]

/-- In `A/U`, `C''` is isomorphic to the represented complex, by `[ιU]` with inverse `[πU]`. -/
def quotIso : (F.proj : InvFunctor A.inv F.quot.inv).mapC c.complex ≅ L.quotComplex :=
  Hom.isoOfComponents
    (fun r ↦ { hom := F.proj.F.map (c.σ r).ιU
               inv := F.proj.F.map (c.σ r).πU
               hom_inv_id := proj_map_ιU_πU _
               inv_hom_id := proj_map_πU_ιU (c.mem r) })
    (fun i j _ ↦ by
      simp only [Functor.mapHomologicalComplex_obj_d, Cascade.uComplex_d, quotComplex_d,
        ← Functor.map_comp, assoc]
      have : L.d i j - L.d i j ≫ (c.σ j).πU ≫ (c.σ j).ιU = L.d i j ≫ (c.σ j).idem := by
        rw [Casc.πU_ιU, comp_sub, comp_id, sub_sub_cancel]
      rw [F.proj_map_eq_iff, ← comp_sub, this, Splitting.idem, ← assoc, ← assoc]
      exact (F.factorsThrough_comp_πE (c.mem j) _).comp_right _)

@[simp] lemma quotIso_hom_f (r : ℤ) : c.quotIso.hom.f r = F.proj.F.map (c.σ r).ιU := rfl
@[simp] lemma quotIso_inv_f (r : ℤ) : c.quotIso.inv.f r = F.proj.F.map (c.σ r).πU := rfl

/-- `quotIso` carries `φ''` to `[φ̃]`. -/
theorem quot_sym : dualHom F.quot.inv N c.quotIso.hom ≫
    (F.proj : InvFunctor A.inv F.quot.inv).mapDual c.sym ≫ c.quotIso.hom = L.quotSym := by
  ext r
  simp only [comp_f, dualHom_f, quotIso_hom_f, InvFunctor.mapDual_f, sym_f, quotSym_f,
    ← F.proj.map_star, F.star_ιU _ _ (c.mem _), Functor.map_comp, assoc]
  rw [proj_map_πU_ιU_assoc (c.mem _), proj_map_πU_ιU (c.mem _), comp_id]

end Cascade

end SymLift

end KaroubiFiltration

/-! ### Lifting strictly symmetric complexes of `A/U` -/

lemma Casc.mapDual_symmetrize {V W : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [Category W] [Preadditive W] [Linear ℚ W] {J : StrictInvolution V} {J' : StrictInvolution W}
    (Φ : InvFunctor J J') [Φ.F.Linear ℚ] (N : ℤ) {C : ChainComplex V ℤ}
    (φ : dualComplex J N C ⟶ C) :
    Φ.mapDual (symmetrize J N φ) = symmetrize J' N (Φ.mapDual φ) := by
  ext r
  simp [symmetrize, Φ.transposeHom_mapDual]

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- The projection `A → A/U` is `ℚ`-linear. -/
lemma proj_linear : F.proj.F.Linear ℚ :=
  inferInstanceAs ((Quotient.functor (factorRel F.U)).Linear ℚ)

/-- A lift to `A` of a morphism of `A/U`, chosen to be `0` on `0`. -/
def liftQuotHom {X Y : A} (f : F.proj.F.obj X ⟶ F.proj.F.obj Y) : X ⟶ Y :=
  open Classical in if f = 0 then 0 else Quot.out f

@[simp]
lemma map_liftQuotHom {X Y : A} (f : F.proj.F.obj X ⟶ F.proj.F.obj Y) :
    F.proj.F.map (F.liftQuotHom f) = f := by
  unfold liftQuotHom
  split_ifs with h
  · rw [h, Functor.map_zero]
  · exact Quot.out_eq f

lemma liftQuotHom_zero {X Y : A} {f : F.proj.F.obj X ⟶ F.proj.F.obj Y} (h : f = 0) :
    F.liftQuotHom f = 0 := by
  unfold liftQuotHom; rw [if_pos h]

namespace SymLift

variable (N) in
/-- Lifting a complex `C` of `A/U`, bounded above, with a chain map `φ : C^{N-*} ⟶ C`: choose
lifts `d̃`, `φ̃` (plan (L1-ii); `A/U` is full on objects and morphisms). -/
@[simps]
def ofQuot (C : ChainComplex F.quot ℤ) (φ : dualComplex F.quot.inv N C ⟶ C) (top : ℤ)
    (hC : ∀ i j, top < i → C.d i j = 0) : F.SymLift N where
  X r := (C.X r).as
  d i j := F.liftQuotHom (C.d i j)
  shape i j h := F.liftQuotHom_zero (C.shape i j h)
  d_comp_d i j k := by
    simpa using (F.proj_map_eq_iff (F.liftQuotHom (C.d i j) ≫ F.liftQuotHom (C.d j k)) 0).mp
      (by erw [Functor.map_comp, map_liftQuotHom, map_liftQuotHom, C.d_comp_d, Functor.map_zero] <;> rfl)
  top := top
  d_eq_zero i j h := F.liftQuotHom_zero (hC i j h)
  φ r := F.liftQuotHom (φ.f r)
  comm r r' := by
    erw [← F.proj_map_eq_iff, Functor.map_comp, Functor.map_comp, Casc.map_units_smul,
      F.proj.map_star, map_liftQuotHom, map_liftQuotHom, map_liftQuotHom, map_liftQuotHom]
    exact φ.comm r r'

variable {F}

/-- The represented complex of `ofQuot` is `C` (identity components). -/
def ofQuotIso (C : ChainComplex F.quot ℤ) (φ : dualComplex F.quot.inv N C ⟶ C) (top : ℤ)
    (hC : ∀ i j, top < i → C.d i j = 0) : (ofQuot F N C φ top hC).quotComplex ≅ C :=
  Hom.isoOfComponents (fun r ↦ Iso.refl _) (fun i j _ ↦ by
    simp only [Iso.refl_hom, quotComplex_d, ofQuot_d]
    erw [id_comp, map_liftQuotHom, comp_id])

lemma ofQuot_quotSym (C : ChainComplex F.quot ℤ) (φ : dualComplex F.quot.inv N C ⟶ C) (top : ℤ)
    (hC : ∀ i j, top < i → C.d i j = 0) :
    (ofQuot F N C φ top hC).quotSym =
      dualHom F.quot.inv N (ofQuotIso C φ top hC).inv ≫ φ ≫ (ofQuotIso C φ top hC).inv := by
  ext r
  simp only [ofQuotIso, comp_f, dualHom_f, quotSym_f, ofQuot_φ, map_liftQuotHom,
    Hom.isoOfComponents_inv_f, Iso.refl_inv]
  erw [F.quot.inv.star_id, id_comp, comp_id, map_liftQuotHom]

namespace Cascade

variable {L : F.SymLift N} (c : L.Cascade)

/-- The strict structure `φ''_s = (φ'' + Tφ'')/2` on `C''`. -/
def liftSym : dualComplex A.inv N c.complex ⟶ c.complex := symmetrize A.inv N c.sym

lemma isStrictSymm_liftSym : IsStrictSymm A.inv N c.liftSym := isStrictSymm_symmetrize _

/-- If `[φ̃]` is strictly symmetric in `A/U`, `quotIso` carries `φ''_s` to it. -/
theorem quot_liftSym (h : IsStrictSymm F.quot.inv N L.quotSym) :
    dualHom F.quot.inv N c.quotIso.hom ≫
      (F.proj : InvFunctor A.inv F.quot.inv).mapDual c.liftSym ≫ c.quotIso.hom = L.quotSym := by
  have := F.proj_linear
  have hT : dualHom F.quot.inv N c.quotIso.hom ≫
      transposeHom F.quot.inv N ((F.proj : InvFunctor A.inv F.quot.inv).mapDual c.sym) ≫
        c.quotIso.hom = L.quotSym := by
    rw [← transposeHom_comp, c.quot_sym, h]
  rw [liftSym, Casc.mapDual_symmetrize, symmetrize]
  simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, c.quot_sym, hT]
  rw [← two_smul ℚ L.quotSym, smul_smul]
  norm_num

end Cascade

end SymLift

/-- **Honest strict lift** (plan (L1-ii)).  A strictly symmetric complex `(C, φ)` of `A/U`,
bounded above, is the image of an honest strictly symmetric complex `(C'', φ'')` of `A`: an
isomorphism `e : F(C'') ≅ C` carries `F φ''` to `φ`.  Here `C'' = (U_σ, ιU d̃ πU)` for a self-dual
cascade `σ` (`SymLift.Cascade.complex`); `d''` and `φ''` vanish wherever `d` and `φ` do, so
support conditions (e.g. a degree truncation idempotent onto `[0, N]`) transfer to `C''`. -/
theorem exists_strictLift (C : ChainComplex F.quot ℤ) (φ : dualComplex F.quot.inv N C ⟶ C)
    (hφ : IsStrictSymm F.quot.inv N φ) (top : ℤ) (hC : ∀ i j, top < i → C.d i j = 0) :
    ∃ (C'' : ChainComplex A ℤ) (φ'' : dualComplex A.inv N C'' ⟶ C'')
      (e : (F.proj : InvFunctor A.inv F.quot.inv).mapC C'' ≅ C),
      IsStrictSymm A.inv N φ'' ∧
      dualHom F.quot.inv N e.hom ≫ (F.proj : InvFunctor A.inv F.quot.inv).mapDual φ'' ≫ e.hom =
        φ ∧ (∀ i j, C.d i j = 0 → C''.d i j = 0) ∧ ∀ r, φ.f r = 0 → φ''.f r = 0 := by
  set L := SymLift.ofQuot F N C φ top hC
  set e₀ := SymLift.ofQuotIso C φ top hC
  have hq : L.quotSym = dualHom F.quot.inv N e₀.inv ≫ φ ≫ e₀.inv := SymLift.ofQuot_quotSym ..
  have hL : IsStrictSymm F.quot.inv N L.quotSym := hq ▸ hφ.conj e₀.inv
  have hφ₀ : ∀ r, φ.f r = 0 → φ.f (N - r) = 0 := fun r h ↦ by
    have h' : φ.f (N - (N - r)) = 0 := by rw [show N - (N - r) = r by omega]; exact h
    rw [← show transposeHom _ N φ = φ from hφ, transposeHom_f, h', StrictInvolution.star_zero,
      zero_comp, smul_zero]
  refine ⟨L.cascade.complex, L.cascade.liftSym, L.cascade.quotIso ≪≫ e₀,
    L.cascade.isStrictSymm_liftSym, ?_, fun i j h ↦ L.cascade.complex_d_eq_zero
      (F.liftQuotHom_zero h), fun r h ↦ ?_⟩
  swap
  · simp only [SymLift.Cascade.liftSym, symmetrize, HomologicalComplex.smul_f_apply,
      HomologicalComplex.add_f_apply, transposeHom_f, SymLift.Cascade.sym_f]
    rw [show L.φ r = 0 from F.liftQuotHom_zero h,
      show L.φ (N - r) = 0 from F.liftQuotHom_zero (hφ₀ r h)]
    simp
  have key := dualHom F.quot.inv N e₀.hom ≫= (L.cascade.quot_liftSym hL =≫ e₀.hom)
  simp only [assoc] at key
  rw [Iso.trans_hom, dualHom_comp]
  simp only [assoc]
  rw [key, hq]
  simp only [assoc, Iso.inv_hom_id, comp_id]
  rw [← assoc, ← dualHom_comp, Iso.inv_hom_id, dualHom_id, id_comp]

end KaroubiFiltration

end

end HSFormal.LTheory
