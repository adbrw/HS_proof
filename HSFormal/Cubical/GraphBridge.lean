import HSFormal.Cubical.Bridge
import HSFormal.Compression
import HSFormal.IntegrationDuality

/-!
# Graph-type families of controlled sequences (manuscript §§8–10)

* `propOn`, `graphPropOn`, `GraphTendsto`: the graph error of §8 (l.544–548) on entries whose
  source lies in a buffered region, for families `u i j` (`j ∈ J i`) of types `θ i j`, uniformly.
  The raw `a_g`, `B_{g,h}` have graph type only there; on regions eventually inside the buffers
  (the retained cells, l.721) it is honest graph type (`GraphTendsto.restrict`,
  `GraphTendsto.quotOfBuffer`).
* `ControlledSeq.graphHom`: the sheet-shifted sum `∑_j u_j ⊗ R_{τ_j⁻¹}` of the degree blocks, a
  morphism of `𝒜_G(X)`, with composition, sums and transposes; `GraphHom.toComplex` and
  `GraphHtpy.toHomotopy` for honest families of chain maps and homotopies.
* `chainMapOfMod`, `homotopyOfMod`: chain maps and homotopies modulo an additive functor; for
  `ℬ_{G,Z}(X)`: `extComplex`, `graphChainMap`, `graphHomotopy`, and `inIdeal_graphHom`.
* Compression (9.1)–(9.6): `quotOfBuffer`/`quot` (`C_i = D_i/F_i`), the matrix identities
  `nearMat_mul`, `nearMat_comm`, `nearMat_htpy` and their family forms
  `commFamily_quotOfBuffer`, `htpyFamily_quotOfBuffer`; the far subcomplex may be `carrierFar`
  (closed carriers missing a set, l.710).
* `nearPart`: the near part of a controlled sequence as a `Compression.NearPart` in `𝒜_G(X)`, with
  `farClosed_nearPart`, `compressed_nearPart`, `far_nearPart`, `compress_graphHom` and the
  residual words `nearPart_word`; `graphHom_relabel` transfers identities between labellings.
* `freeSheet_toComplex`, `exteriorFreeSheet_extComplex`: `Ind` of (10.1) on these complexes.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory
open scoped ENNReal Topology

/-! ### Graph errors on a buffered region -/

section PropOn

variable {H X A B C : Type*} [PseudoEMetricSpace X] {u v : Matrix B A ℚ} {source : A → X}
  {target : B → X} {buf buf' : A → Prop}

/-- Propagation over the entries whose source lies in `buf`. -/
def propOn (buf : A → Prop) (u : Matrix B A ℚ) (source : A → X) (target : B → X) : ℝ≥0∞ :=
  ⨆ (b) (a) (_ : buf a) (_ : u b a ≠ 0), edist (target b) (source a)

theorem propOn_le_iff {r : ℝ≥0∞} :
    propOn buf u source target ≤ r ↔
      ∀ b a, buf a → u b a ≠ 0 → edist (target b) (source a) ≤ r := by
  simp only [propOn, iSup_le_iff]

theorem edist_le_propOn {b : B} {a : A} (ha : buf a) (h : u b a ≠ 0) :
    edist (target b) (source a) ≤ propOn buf u source target :=
  propOn_le_iff.mp le_rfl b a ha h

theorem propOn_le_prop : propOn buf u source target ≤ prop u source target :=
  propOn_le_iff.mpr fun _ _ _ h ↦ edist_le_prop h

@[simp]
theorem propOn_true : propOn (fun _ ↦ True) u source target = prop u source target :=
  le_antisymm propOn_le_prop (prop_le_iff.mpr fun _ _ h ↦ edist_le_propOn trivial h)

theorem propOn_mono (h : ∀ a, buf a → buf' a) :
    propOn buf u source target ≤ propOn buf' u source target :=
  propOn_le_iff.mpr fun _ _ ha hu ↦ edist_le_propOn (h _ ha) hu

@[simp]
theorem propOn_zero : propOn buf (0 : Matrix B A ℚ) source target = 0 :=
  le_antisymm (propOn_le_iff.mpr fun _ _ _ h ↦ (h rfl).elim) bot_le

theorem propOn_add_le :
    propOn buf (u + v) source target ≤
      max (propOn buf u source target) (propOn buf v source target) :=
  propOn_le_iff.mpr fun b a ha h ↦ by
    by_cases hu : u b a = 0
    · exact (edist_le_propOn ha (by simpa [hu] using h)).trans (le_max_right _ _)
    · exact (edist_le_propOn ha hu).trans (le_max_left _ _)

theorem propOn_smul_le (c : ℚ) : propOn buf (c • u) source target ≤ propOn buf u source target :=
  propOn_le_iff.mpr fun _ _ ha h ↦ edist_le_propOn ha (right_ne_zero_of_mul h)

@[simp]
theorem propOn_neg : propOn buf (-u) source target = propOn buf u source target := by
  simp [propOn]

theorem propOn_sub_le :
    propOn buf (u - v) source target ≤
      max (propOn buf u source target) (propOn buf v source target) := by
  simpa [sub_eq_add_neg] using propOn_add_le (u := u) (v := -v)

/-- **Restriction to a region inside the buffer gives honest control.** -/
theorem prop_submatrix_le_propOn {A' B' : Type*} (f : A' → A) (g : B' → B) (hf : ∀ a, buf (f a)) :
    prop (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ propOn buf u source target :=
  prop_le_iff.mpr fun _ a h ↦ edist_le_propOn (hf a) h

theorem propOn_submatrix_le {A' B' : Type*} (f : A' → A) (g : B' → B) :
    propOn (buf ∘ f) (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ propOn buf u source target :=
  propOn_le_iff.mpr fun b a ha h ↦ edist_le_propOn (u := u) (b := g b) (a := f a) ha h

/-- Composition, when `u` maps the buffer `buf` into the buffer `buf'`. -/
theorem propOn_mul_le [Fintype B] {bufB : B → Prop} (w : Matrix C B ℚ) (middle : B → X)
    (target' : C → X) (hbuf : ∀ b a, buf a → u b a ≠ 0 → bufB b) :
    propOn buf (w * u) source target' ≤ propOn buf u source middle + propOn bufB w middle target' :=
  propOn_le_iff.mpr fun c a ha h ↦ by
    obtain ⟨b, hw, hu⟩ := matrix_mul_entry_nonzero_witness u w c a h
    calc edist (target' c) (source a)
        ≤ edist (target' c) (middle b) + edist (middle b) (source a) := edist_triangle _ _ _
      _ ≤ _ := by
          rw [add_comm]
          exact add_le_add (edist_le_propOn ha hu) (edist_le_propOn (hbuf b a ha hu) hw)

theorem propOn_sum_le {ι : Type*} (s : Finset ι) (w : ι → Matrix B A ℚ) :
    propOn buf (∑ j ∈ s, w j) source target ≤ ⨆ j ∈ s, propOn buf (w j) source target :=
  propOn_le_iff.mpr fun b a ha hba ↦ by
    rw [Matrix.sum_apply] at hba
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hba
    exact (edist_le_propOn ha hne).trans (le_iSup₂_of_le j hj le_rfl)

variable [Group H] [MulAction H X]

/-- The graph-type-`h` error of §8 (l.546) on the entries whose source lies in the buffered
region `buf`; for `buf = ⊤` it is `graphProp`. -/
def graphPropOn (buf : A → Prop) (h : H) (u : Matrix B A ℚ) (source : A → X) (target : B → X) :
    ℝ≥0∞ :=
  propOn buf u (fun a ↦ h • source a) target

theorem graphPropOn_le_iff {h : H} {r : ℝ≥0∞} :
    graphPropOn buf h u source target ≤ r ↔
      ∀ b a, buf a → u b a ≠ 0 → edist (target b) (h • source a) ≤ r :=
  propOn_le_iff

theorem graphPropOn_le_graphProp (h : H) :
    graphPropOn buf h u source target ≤ graphProp h u source target :=
  propOn_le_prop

@[simp]
theorem graphPropOn_true (h : H) :
    graphPropOn (fun _ ↦ True) h u source target = graphProp h u source target :=
  propOn_true

@[simp]
theorem graphPropOn_one : graphPropOn buf (1 : H) u source target = propOn buf u source target := by
  simp [graphPropOn]

/-- **Graph type on the buffer becomes honest graph type on a region inside the buffer**, e.g.
the retained cells of `C_i = D_i/F_i` (§9, l.721). -/
theorem graphProp_submatrix_le_graphPropOn {A' B' : Type*} (f : A' → A) (g : B' → B)
    (hf : ∀ a, buf (f a)) (h : H) :
    graphProp h (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ graphPropOn buf h u source target :=
  prop_submatrix_le_propOn (source := fun a ↦ h • source a) f g hf

/-- For `X = T × Y` with `H` acting trivially on `Y`: the `Y`-coordinates approach each other and
`d_T(target, h • source)` is small, on the buffer (l.546). -/
theorem graphPropOn_prod_le_iff {T Y : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace Y]
    [MulAction H T] [MulAction H Y] (htriv : ∀ (h : H) (y : Y), h • y = y)
    {source : A → T × Y} {target : B → T × Y} {h : H} {r : ℝ≥0∞} :
    graphPropOn buf h u source target ≤ r ↔ ∀ b a, buf a → u b a ≠ 0 →
      edist (target b).1 (h • (source a).1) ≤ r ∧ edist (target b).2 (source a).2 ≤ r := by
  simp only [graphPropOn_le_iff, Prod.edist_eq, max_le_iff, Prod.smul_fst, Prod.smul_snd, htriv]

/-- **Graph types multiply** on buffers preserved by the first factor. -/
theorem graphPropOn_mul_le [IsIsometricSMul H X] [Fintype B] {bufB : B → Prop} (g h : H)
    (w : Matrix C B ℚ) (middle : B → X) (target' : C → X)
    (hbuf : ∀ b a, buf a → u b a ≠ 0 → bufB b) :
    graphPropOn buf (g * h) (w * u) source target' ≤
      graphPropOn buf h u source middle + graphPropOn bufB g w middle target' :=
  graphPropOn_le_iff.mpr fun c a ha hca ↦ by
    obtain ⟨b, hw, hu⟩ := matrix_mul_entry_nonzero_witness u w c a hca
    calc edist (target' c) ((g * h) • source a)
        ≤ edist (target' c) (g • middle b) + edist (g • middle b) ((g * h) • source a) :=
          edist_triangle _ _ _
      _ = edist (target' c) (g • middle b) + edist (middle b) (h • source a) := by
          rw [← smul_smul, edist_smul_left]
      _ ≤ _ := by
          rw [add_comm]
          exact add_le_add (graphPropOn_le_iff.mp le_rfl b a ha hu)
            (graphPropOn_le_iff.mp le_rfl c b (hbuf b a ha hu) hw)

end PropOn

/-! ### Families of uniform graph type on buffers -/

section Seq

variable {H X : Type*} [Group H] [MulAction H X] [PseudoEMetricSpace X]
  {α β γ : ℕ → Type*} {J J' : ℕ → Type*}

/-- Propagation tending to zero on the buffers `buf i`. -/
def PropTendstoOn (buf : ∀ i, α i → Prop) (u : ∀ i, Matrix (β i) (α i) ℚ) (a : ∀ i, α i → X)
    (b : ∀ i, β i → X) : Prop :=
  Tendsto (fun i ↦ propOn (buf i) (u i) (a i) (b i)) atTop (𝓝 0)

/-- The uniform graph error `sup_j` of a family `u i j` of types `θ i j` on the buffers. -/
def graphErr (buf : ∀ i, α i → Prop) (θ : ∀ i, J i → H) (u : ∀ i, J i → Matrix (β i) (α i) ℚ)
    (a : ∀ i, α i → X) (b : ∀ i, β i → X) (i : ℕ) : ℝ≥0∞ :=
  ⨆ j, graphPropOn (buf i) (θ i j) (u i j) (a i) (b i)

/-- Manuscript §8 (l.544–548, 633, 664): `u i j` has graph type `θ i j` on the buffered regions
`buf i`, uniformly in `j` and `i`.  For `buf = ⊤` this is honest graph type. -/
def GraphTendsto (buf : ∀ i, α i → Prop) (θ : ∀ i, J i → H)
    (u : ∀ i, J i → Matrix (β i) (α i) ℚ) (a : ∀ i, α i → X) (b : ∀ i, β i → X) : Prop :=
  Tendsto (graphErr buf θ u a b) atTop (𝓝 0)

variable {buf buf' : ∀ i, α i → Prop} {θ θ' : ∀ i, J i → H}
  {u u' : ∀ i, J i → Matrix (β i) (α i) ℚ} {a : ∀ i, α i → X} {b : ∀ i, β i → X}
  {c : ∀ i, γ i → X}

theorem graphPropOn_le_graphErr (i : ℕ) (j : J i) :
    graphPropOn (buf i) (θ i j) (u i j) (a i) (b i) ≤ graphErr buf θ u a b i :=
  le_iSup (fun j ↦ graphPropOn (buf i) (θ i j) (u i j) (a i) (b i)) j

theorem graphErr_le_iff {i : ℕ} {r : ℝ≥0∞} :
    graphErr buf θ u a b i ≤ r ↔
      ∀ j y x, buf i x → u i j y x ≠ 0 → edist (b i y) (θ i j • a i x) ≤ r := by
  simp only [graphErr, iSup_le_iff, graphPropOn_le_iff]

namespace GraphTendsto

/-- Graph type from explicit carrier bounds, eventually in `i`. -/
theorem of_le {e : ℕ → ℝ≥0∞} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ i in atTop, ∀ j y x, buf i x → u i j y x ≠ 0 → edist (b i y) (θ i j • a i x) ≤ e i) :
    GraphTendsto buf θ u a b :=
  tendsto_zero_of_eventually_le he (h.mono fun _ ↦ graphErr_le_iff.mpr)

theorem mono_buf (hu : GraphTendsto buf θ u a b) (h : ∀ᶠ i in atTop, ∀ x, buf' i x → buf i x) :
    GraphTendsto buf' θ u a b :=
  tendsto_zero_of_eventually_le hu <| h.mono fun _ hi ↦ iSup_mono fun _ ↦ propOn_mono hi

theorem reindex (hu : GraphTendsto buf θ u a b) (e : ∀ i, J' i → J i) :
    GraphTendsto buf (fun i j ↦ θ i (e i j)) (fun i j ↦ u i (e i j)) a b :=
  tendsto_zero_of_le hu fun i ↦ iSup_le fun j ↦ graphPropOn_le_graphErr (θ := θ) (u := u) i (e i j)

theorem add (hu : GraphTendsto buf θ u a b) (hu' : GraphTendsto buf θ u' a b) :
    GraphTendsto buf θ (fun i j ↦ u i j + u' i j) a b :=
  tendsto_zero_of_le (by simpa using hu.max hu') fun i ↦ iSup_le fun j ↦
    propOn_add_le.trans (max_le_max (graphPropOn_le_graphErr i j) (graphPropOn_le_graphErr i j))

/-- Coefficients are unrestricted (manuscript §2). -/
theorem smul (k : ∀ i, J i → ℚ) (hu : GraphTendsto buf θ u a b) :
    GraphTendsto buf θ (fun i j ↦ k i j • u i j) a b :=
  tendsto_zero_of_le hu fun i ↦ iSup_le fun j ↦
    (propOn_smul_le _).trans (graphPropOn_le_graphErr i j)

theorem neg (hu : GraphTendsto buf θ u a b) : GraphTendsto buf θ (fun i j ↦ -u i j) a b := by
  have : graphErr buf θ (fun i j ↦ -u i j) a b = graphErr buf θ u a b :=
    funext fun _ ↦ by simp [graphErr, graphPropOn]
  rwa [GraphTendsto, this]

theorem sub (hu : GraphTendsto buf θ u a b) (hu' : GraphTendsto buf θ u' a b) :
    GraphTendsto buf θ (fun i j ↦ u i j - u' i j) a b := by
  simpa [sub_eq_add_neg] using hu.add hu'.neg

theorem zero : GraphTendsto buf θ (fun _ _ ↦ (0 : Matrix (β _) (α _) ℚ)) a b :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ le_antisymm (iSup_le fun _ ↦ by simp [graphPropOn]) bot_le

theorem congr (hu : GraphTendsto buf θ u a b) (hθ : θ = θ') (hu' : u = u') :
    GraphTendsto buf θ' u' a b := hθ ▸ hu' ▸ hu

/-- **Restriction to regions eventually inside the buffers gives honest graph type** (§9,
l.721: retained cells eventually lie in the domain of `ρ̃`). -/
theorem restrict {α' β' : ℕ → Type*} (hu : GraphTendsto buf θ u a b) (f : ∀ i, α' i → α i)
    (g : ∀ i, β' i → β i) (hf : ∀ᶠ i in atTop, ∀ x, buf i (f i x)) :
    GraphTendsto (fun _ _ ↦ True) θ (fun i j ↦ (u i j).submatrix (g i) (f i))
      (fun i ↦ a i ∘ f i) (fun i ↦ b i ∘ g i) :=
  tendsto_zero_of_eventually_le hu <| hf.mono fun i hi ↦ iSup_le fun j ↦ by
    rw [graphPropOn_true]
    exact (graphProp_submatrix_le_graphPropOn (f i) (g i) hi _).trans
      (graphPropOn_le_graphErr i j)

variable [IsIsometricSMul H X] [∀ i, Fintype (β i)]

/-- **Graph types multiply**, for all composites `v_{j'} u_j`, provided the first factors map the
buffers into the buffers of the second. -/
theorem prodMul {bufB : ∀ i, β i → Prop} {θ' : ∀ i, J' i → H}
    {v : ∀ i, J' i → Matrix (γ i) (β i) ℚ} (hu : GraphTendsto buf θ u a b)
    (hv : GraphTendsto bufB θ' v b c)
    (hbuf : ∀ᶠ i in atTop, ∀ j y x, buf i x → u i j y x ≠ 0 → bufB i y) :
    GraphTendsto (J := fun i ↦ J i × J' i) buf (fun i p ↦ θ' i p.2 * θ i p.1)
      (fun i p ↦ v i p.2 * u i p.1) a c :=
  tendsto_zero_of_eventually_le (by simpa using Filter.Tendsto.add hu hv) <| hbuf.mono fun i hi ↦
    iSup_le fun p ↦ (graphPropOn_mul_le _ _ _ (b i) _ (hi p.1)).trans
      (add_le_add (graphPropOn_le_graphErr i p.1) (graphPropOn_le_graphErr i p.2))

/-- **Graph types multiply**, index by index. -/
theorem mul {bufB : ∀ i, β i → Prop} {v : ∀ i, J i → Matrix (γ i) (β i) ℚ}
    (hu : GraphTendsto buf θ u a b) (hv : GraphTendsto bufB θ' v b c)
    (hbuf : ∀ᶠ i in atTop, ∀ j y x, buf i x → u i j y x ≠ 0 → bufB i y) :
    GraphTendsto buf (fun i j ↦ θ' i j * θ i j) (fun i j ↦ v i j * u i j) a c :=
  tendsto_zero_of_le (hu.prodMul hv hbuf) fun _ ↦ iSup_le fun j ↦
    le_iSup_of_le (j, j) le_rfl

omit [∀ i, Fintype (β i)] in
/-- **Duality inverts graph types** (honest families). -/
theorem transpose (hu : GraphTendsto (fun _ _ ↦ True) θ u a b) :
    GraphTendsto (fun _ _ ↦ True) (fun i j ↦ (θ i j)⁻¹) (fun i j ↦ (u i j)ᵀ) b a := by
  have : graphErr (fun _ _ ↦ True) (fun i j ↦ (θ i j)⁻¹) (fun i j ↦ (u i j)ᵀ) b a =
      graphErr (fun _ _ ↦ True) θ u a b :=
    funext fun _ ↦ by simp [graphErr]
  rwa [GraphTendsto, this]

end GraphTendsto

namespace PropTendstoOn

variable {w : ∀ i, Matrix (β i) (α i) ℚ}

theorem mono_buf (hw : PropTendstoOn buf w a b) (h : ∀ᶠ i in atTop, ∀ x, buf' i x → buf i x) :
    PropTendstoOn buf' w a b :=
  tendsto_zero_of_eventually_le hw <| h.mono fun _ hi ↦ propOn_mono hi

/-- A type-`1` sequence as a constant family. -/
theorem graphTendsto (hw : PropTendstoOn buf w a b) :
    GraphTendsto (J := J) buf (fun _ _ ↦ (1 : H)) (fun i _ ↦ w i) a b :=
  tendsto_zero_of_le hw fun _ ↦ iSup_le fun _ ↦ graphPropOn_one.le

/-- Restriction to regions eventually inside the buffers gives honest control. -/
theorem restrict {α' β' : ℕ → Type*} (hw : PropTendstoOn buf w a b) (f : ∀ i, α' i → α i)
    (g : ∀ i, β' i → β i) (hf : ∀ᶠ i in atTop, ∀ x, buf i (f i x)) :
    Tendsto (fun i ↦ prop ((w i).submatrix (g i) (f i)) (a i ∘ f i) (b i ∘ g i)) atTop (𝓝 0) :=
  tendsto_zero_of_eventually_le hw <| hf.mono fun _ hi ↦ prop_submatrix_le_propOn _ _ hi

end PropTendstoOn

namespace GraphTendsto

variable [IsIsometricSMul H X] [∀ i, Fintype (β i)]

/-- A type-`1` factor on the left. -/
theorem mul_left {bufB : ∀ i, β i → Prop} {w : ∀ i, Matrix (γ i) (β i) ℚ}
    (hw : PropTendstoOn bufB w b c) (hu : GraphTendsto buf θ u a b)
    (hbuf : ∀ᶠ i in atTop, ∀ j y x, buf i x → u i j y x ≠ 0 → bufB i y) :
    GraphTendsto buf θ (fun i j ↦ w i * u i j) a c := by
  simpa using hu.mul (hw.graphTendsto (H := H)) hbuf

omit [∀ i, Fintype (β i)] in
/-- A type-`1` factor on the right. -/
theorem mul_right {w : ∀ i, Matrix (α i) (γ i) ℚ} [∀ i, Fintype (α i)] {bufC : ∀ i, γ i → Prop}
    {d : ∀ i, γ i → X} (hw : PropTendstoOn bufC w d a) (hu : GraphTendsto buf θ u a b)
    (hbuf : ∀ᶠ i in atTop, ∀ x z, bufC i z → w i x z ≠ 0 → buf i x) :
    GraphTendsto bufC θ (fun i j ↦ u i j * w i) d b := by
  simpa using (hw.graphTendsto (J := J) (H := H)).mul hu (hbuf.mono fun _ hi _ ↦ hi)

end GraphTendsto

end Seq

namespace AsymptoticObject

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] {π : ∀ i, G i →* H}
  {X : Type*} [MulAction H X] [PseudoEMetricSpace X] {M N : AsymptoticObject π X}
  {J : ℕ → Type*} {τ : ∀ i, J i → G i}

theorem hasGraphType_iff_graphTendsto {a : GraphFamily J M N} :
    HasGraphType τ a ↔
      GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) a M.label N.label := by
  have : graphPropSeq τ a = graphErr (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) a M.label N.label :=
    funext fun _ ↦ by simp [graphPropSeq, graphErr]
  rw [HasGraphType, GraphTendsto, this]

end AsymptoticObject

/-! ### Chain maps and homotopies modulo an additive functor -/

section Mod

variable {V W : Type*} [Category V] [Category W] [Preadditive V] [Preadditive W] (F : V ⥤ W)
  [F.Additive] {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex V c}

/-- Degreewise maps commuting with the differentials after `F` (e.g. modulo `I_Z`) give a chain
map of the image complexes. -/
@[simps]
def chainMapOfMod (f : ∀ i, K.X i ⟶ L.X i)
    (hf : ∀ i j, c.Rel i j → F.map (f i ≫ L.d i j) = F.map (K.d i j ≫ f j)) :
    (F.mapHomologicalComplex c).obj K ⟶ (F.mapHomologicalComplex c).obj L where
  f i := F.map (f i)
  comm' i j hij := by
    simp only [Functor.mapHomologicalComplex_obj_d, ← F.map_comp]
    exact hf i j hij

/-- Homotopies modulo `F`: `F (f - g - (dh + hd)) = 0`. -/
@[simps]
def homotopyOfMod {f g : ∀ i, K.X i ⟶ L.X i} (hf hg) (h : ∀ i j, K.X i ⟶ L.X j)
    (hzero : ∀ i j, ¬c.Rel j i → h i j = 0)
    (hcomm : ∀ i, F.map (f i) = F.map (dNext i h + prevD i h + g i)) :
    Homotopy (chainMapOfMod F f hf) (chainMapOfMod F g hg) where
  hom i j := F.map (h i j)
  zero i j hij := by rw [hzero i j hij, F.map_zero]
  comm i := by
    have H := hcomm i
    dsimp [dNext, prevD] at H ⊢
    simp [H]

theorem chainMapOfMod_comp {M : HomologicalComplex V c} {f : ∀ i, K.X i ⟶ L.X i}
    {g : ∀ i, L.X i ⟶ M.X i} (hf hg) (hfg) :
    chainMapOfMod F f hf ≫ chainMapOfMod F g hg = chainMapOfMod F (fun i ↦ f i ≫ g i) hfg := by
  ext i; simp

theorem chainMapOfMod_add {f g : ∀ i, K.X i ⟶ L.X i} (hf hg) (hfg) :
    chainMapOfMod F f hf + chainMapOfMod F g hg = chainMapOfMod F (fun i ↦ f i + g i) hfg := by
  ext i; simp

theorem chainMapOfMod_ext {f g : ∀ i, K.X i ⟶ L.X i} (hf hg) (h : ∀ i, F.map (f i) = F.map (g i)) :
    chainMapOfMod F f hf = chainMapOfMod F g hg := by
  ext i; exact h i

/-- A chain map before `F`. -/
theorem chainMapOfMod_hom (φ : K ⟶ L) (hf) :
    chainMapOfMod F φ.f hf = (F.mapHomologicalComplex c).map φ := rfl

end Mod

namespace AsymptoticObject

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] (π : ∀ i, G i →* H)
  {X : Type*} [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] (Z : Set X)

/-- The quotient functor `𝒜_G(X) → ℬ_{G,Z}(X)` on honest controlled families. -/
abbrev extFunctor : AsymptoticObject π X ⥤ ExteriorCategory π Z :=
  AsymptoticCategory.functor ⋙ ExteriorCategory.functor

variable {π Z}

/-- Equality in `ℬ_{G,Z}(X)` is an exterior witness for the difference. -/
theorem extFunctor_map_eq_iff {M N : AsymptoticObject π X} (f g : M ⟶ N) :
    (extFunctor π Z).map f = (extFunctor π Z).map g ↔
      AsymptoticCategory.InIdeal Z (AsymptoticCategory.functor.map (f - g)) := by
  rw [Functor.comp_map, Functor.comp_map, ExteriorCategory.functor_map_eq_iff, Functor.map_sub]

theorem extFunctor_map_eq_zero_iff {M N : AsymptoticObject π X} (f : M ⟶ N) :
    (extFunctor π Z).map f = 0 ↔
      AsymptoticCategory.InIdeal Z (AsymptoticCategory.functor.map f) := by
  rw [← (extFunctor π Z).map_zero, extFunctor_map_eq_iff, sub_zero]

end AsymptoticObject

end HSFormal

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory HSFormal.AsymptoticObject
open scoped ENNReal Topology Pointwise

namespace BasedComplex

/-! ### Degree blocks -/

section Block

variable {C D E : BasedComplex}

/-- The degree-`r → r'` block of a matrix, on the enumerated cells. -/
def blockMat (u : Matrix D.X C.X ℚ) (r r' : ℤ) :
    Matrix (Fin (Fintype.card (Cells D r'))) (Fin (Fintype.card (Cells C r))) ℚ :=
  u.submatrix (fun k ↦ ((cellEquiv D r').symm k).1) (fun k ↦ ((cellEquiv C r).symm k).1)

theorem blockMat_mul (u : Matrix D.X C.X ℚ) (v : Matrix E.X D.X ℚ) {r r' r'' : ℤ}
    (h : ∀ κ σ, u κ σ ≠ 0 → (C.deg σ : ℤ) = r → (D.deg κ : ℤ) = r') :
    blockMat (v * u) r r'' = blockMat v r' r'' * blockMat u r r' := by
  ext k'' k
  simp only [blockMat, submatrix_apply, mul_apply]
  exact (sum_cells _ _ (fun κ ↦ v _ κ * u κ _) fun κ hκ ↦
    h κ _ (right_ne_zero_of_mul hκ) ((cellEquiv C r).symm k).2).symm

theorem blockMat_one (r : ℤ) : blockMat (1 : Matrix C.X C.X ℚ) r r = 1 := by
  ext k' k
  simp only [blockMat, submatrix_apply, one_apply, Subtype.val_inj, Equiv.apply_eq_iff_eq]

theorem blockMat_eq_zero {u : Matrix D.X C.X ℚ} {r r' : ℤ}
    (h : ∀ κ σ, (C.deg σ : ℤ) = r → (D.deg κ : ℤ) = r' → u κ σ = 0) : blockMat u r r' = 0 := by
  ext k' k
  exact h _ _ ((cellEquiv C r).symm k).2 ((cellEquiv D r').symm k').2

theorem blockMat_transpose (u : Matrix D.X C.X ℚ) (r r' : ℤ) :
    blockMat uᵀ r' r = (blockMat u r r')ᵀ := rfl

end Block

namespace ControlledSeq

variable {X : Type*} [PseudoEMetricSpace X] {A B B' : ControlledSeq X}

theorem _root_.HSFormal.Cubical.BasedComplex.PropTendsto.on {C D : ℕ → BasedComplex}
    {u : ∀ i, Matrix (D i).X (C i).X ℚ} {a : ∀ i, (C i).X → X} {b : ∀ i, (D i).X → X}
    (hu : PropTendsto u a b) (buf : ∀ i, (C i).X → Prop) : PropTendstoOn buf u a b :=
  tendsto_zero_of_le hu fun _ ↦ propOn_le_prop

/-! ### Shifted graph-type families of blocks in `𝒜_G(X)` -/

section GraphHom

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] (π : ∀ i, G i →* H)
  [MulAction H X] [IsIsometricSMul H X] [∀ i, Fintype (G i)] {J J' : ℕ → Type*}
  [∀ i, Fintype (J i)] [∀ i, Fintype (J' i)] {τ τ' : ∀ i, J i → G i}

/-- The family of degree blocks of `u i j`. -/
def gblock (u : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ) (r r' : ℤ) :
    GraphFamily J (A.obj π r) (B.obj π r') :=
  fun i j ↦ blockMat (u i j) r r'

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] [∀ i, Fintype (J i)] in
theorem hasGraphType_gblock {u : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ}
    (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label) (r r' : ℤ) :
    HasGraphType τ (gblock π u r r') :=
  hasGraphType_iff_graphTendsto.mpr <| hu.restrict _ _ (Eventually.of_forall fun _ _ ↦ trivial)

/-- The sheet-shifted sum `∑_j u i j ⊗ R_{(τ i j)⁻¹}` of the degree blocks (§10): honest graph
types become morphisms of `𝒜_G(X)`. -/
def graphHom (τ : ∀ i, J i → G i) (u : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ)
    (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label) (r r' : ℤ) :
    A.obj π r ⟶ B.obj π r' :=
  graphSum τ (gblock π u r r') (hasGraphType_gblock π hu r r')

variable {π} {u u' : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ}

theorem graphHom_val (hu) (r r' : ℤ) (i : ℕ) :
    (graphHom π τ u hu r r').1 i = ∑ j, sheet (τ i j) (blockMat (u i j) r r') := rfl

/-- Morphisms built from the same blocks are equal; blocks do not see the labels. -/
theorem graphHom_eq_of_blockMat {r r' : ℤ} (hu hu')
    (h : ∀ i j, blockMat (u i j) r r' = blockMat (u' i j) r r') :
    graphHom π τ u hu r r' = graphHom π τ u' hu' r r' :=
  hom_ext fun i ↦ by simp only [graphHom_val, h]

theorem graphHom_congr (hτ : τ = τ') (hu' : u = u') (hu h') (r r' : ℤ) :
    graphHom π τ u hu r r' = graphHom π τ' u' h' r r' := by
  subst hτ hu'; rfl

theorem graphHom_eq_zero (hu) {r r' : ℤ}
    (h : ∀ i j κ σ, (A.C i).deg σ = r → (B.C i).deg κ = r' → u i j κ σ = 0) :
    graphHom π τ u hu r r' = 0 :=
  hom_ext fun i ↦ by
    simp [graphHom_val, blockMat_eq_zero (h i _)]

/-- A sequence on one sheet is the type-`1` shifted sum over a point. -/
theorem hom_eq_graphHom (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu : PropTendsto u A.label B.label)
    (r r' : ℤ) :
    hom π u hu r r' = graphHom π (J := fun _ ↦ Unit) (fun _ _ ↦ 1) (fun i _ ↦ u i)
      (by simpa using (hu.on (fun _ _ ↦ True)).graphTendsto (H := H)) r r' :=
  hom_ext fun i ↦ by simp [graphHom_val, hom_val]; rfl

theorem graphHom_add (hu hu') (r r' : ℤ) :
    graphHom π τ u hu r r' + graphHom π τ u' hu' r r' =
      graphHom π τ (fun i j ↦ u i j + u' i j) (hu.add hu') r r' :=
  graphSum_add _ _

theorem graphHom_sub (hu hu') (r r' : ℤ) :
    graphHom π τ u hu r r' - graphHom π τ u' hu' r r' =
      graphHom π τ (fun i j ↦ u i j - u' i j) (hu.sub hu') r r' :=
  graphSum_sub _ _

theorem graphHom_neg (hu) (r r' : ℤ) :
    -graphHom π τ u hu r r' = graphHom π τ (fun i j ↦ -u i j) hu.neg r r' :=
  hom_ext fun i ↦ by simp [graphHom_val, sheet_neg, blockMat, submatrix_neg]

theorem graphHom_smul (c : ℚ) (hu) (r r' : ℤ) :
    c • graphHom π τ u hu r r' = graphHom π τ (fun i j ↦ c • u i j) (hu.smul fun _ _ ↦ c) r r' :=
  graphSum_smul _ _

/-- A type-`1` map followed by a shifted family. -/
theorem hom_comp_graphHom (w : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hw)
    {v : ∀ i, J i → Matrix (B'.C i).X (B.C i).X ℚ} (hv) {r r' r'' : ℤ}
    (h : ∀ i κ σ, w i κ σ ≠ 0 → (A.C i).deg σ = r → (B.C i).deg κ = r') :
    hom π w hw r r' ≫ graphHom π τ v hv r' r'' =
      graphHom π τ (fun i j ↦ v i j * w i)
        (hv.mul_right (hw.on _) (Eventually.of_forall fun _ _ _ _ _ ↦ trivial)) r r'' :=
  hom_ext fun i ↦ by
    rw [comp_val, graphHom_val, graphHom_val, hom_val, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sheet_mul, mul_one, blockMat_mul _ _ (h i)]
    rfl

/-- A shifted family followed by a type-`1` map. -/
theorem graphHom_comp_hom (hu) (w : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ) (hw) {r r' r'' : ℤ}
    (h : ∀ i j κ σ, u i j κ σ ≠ 0 → (A.C i).deg σ = r → (B.C i).deg κ = r') :
    graphHom π τ u hu r r' ≫ hom π w hw r' r'' =
      graphHom π τ (fun i j ↦ w i * u i j)
        (hu.mul_left (hw.on _) (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)) r r'' :=
  hom_ext fun i ↦ by
    rw [comp_val, graphHom_val, graphHom_val, hom_val, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sheet_mul, one_mul, blockMat_mul _ _ (h i j)]
    rfl

/-- Shifted families compose over the product index, with types `τ' τ`. -/
theorem graphHom_comp (hu) {τ' : ∀ i, J' i → G i} {v : ∀ i, J' i → Matrix (B'.C i).X (B.C i).X ℚ}
    (hv) {r r' r'' : ℤ} (h : ∀ i j κ σ, u i j κ σ ≠ 0 → (A.C i).deg σ = r → (B.C i).deg κ = r') :
    graphHom π τ u hu r r' ≫ graphHom π τ' v hv r' r'' =
      graphHom π (J := fun i ↦ J i × J' i) (fun i p ↦ τ' i p.2 * τ i p.1)
        (fun i p ↦ v i p.2 * u i p.1)
        (by simpa using hu.prodMul hv (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)) r r'' := by
  rw [graphHom, graphHom, graphSum_comp]
  refine hom_ext fun i ↦ ?_
  rw [graphSum_val, graphHom_val]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [blockMat_mul _ _ (h i p.1)]
  rfl

/-- Duality inverts graph types and reverses the sheet translation. -/
theorem transpose_graphHom (hu) (r r' : ℤ) :
    AsymptoticObject.transpose (graphHom π τ u hu r r') =
      graphHom π (fun i j ↦ (τ i j)⁻¹) (fun i j ↦ (u i j)ᵀ) (by simpa using hu.transpose) r' r :=
  transpose_graphSum _

end GraphHom

/-! ### Graph-type chain maps and homotopies -/

section Families

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] (π : ∀ i, G i →* H)
  [MulAction H X] {J J' : ℕ → Type*} {τ : ∀ i, J i → G i}

/-- Families of controlled chain maps `F i j : A_i → B_i` of uniform graph type `τ i j` (§8),
e.g. the raw `a_g` (`J i = G i`, `τ i = id`) in the `f`-labels. -/
structure GraphHom (τ : ∀ i, J i → G i) (A B : ControlledSeq X) where
  f : ∀ i, J i → BasedComplex.Hom (A.C i) (B.C i)
  tendsto : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) (fun i j ↦ (f i j).f)
    A.label B.label

/-- Families of controlled exact homotopies of uniform graph type, e.g. `B_{g,h}` of (8.5). -/
structure GraphHtpy (F F' : GraphHom π τ A B) where
  h : ∀ i j, BasedComplex.Htpy (F.f i j) (F'.f i j)
  tendsto : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) (fun i j ↦ (h i j).h)
    A.label B.label

namespace GraphHom

variable {π}

/-- A controlled chain map as a constant family of type `1`. -/
def ofHom (F : Hom A B) : GraphHom π (J := J) (fun _ _ ↦ 1) A B :=
  ⟨fun i _ ↦ F.f i, by simpa using (F.tendsto.on fun _ _ ↦ True).graphTendsto (J := J) (H := H)⟩

/-- Sums of families of the same types. -/
def add (F F' : GraphHom π τ A B) : GraphHom π τ A B :=
  ⟨fun i j ↦ (F.f i j).add (F'.f i j), F.tendsto.add F'.tendsto⟩

/-- Rescaling, e.g. by `|G_i|⁻¹` in (10.2). -/
def smul (c : ∀ i, J i → ℚ) (F : GraphHom π τ A B) : GraphHom π τ A B :=
  ⟨fun i j ↦ (F.f i j).smul (c i j), F.tendsto.smul c⟩

/-- Reindexing, e.g. `(g, h) ↦ gh`. -/
def reindex (F : GraphHom π τ A B) (e : ∀ i, J' i → J i) :
    GraphHom π (fun i j ↦ τ i (e i j)) A B :=
  ⟨fun i j ↦ F.f i (e i j), F.tendsto.reindex e⟩

/-- All composites `F'_{j'} F_j`, of types `τ' τ`. -/
def comp [IsIsometricSMul H X] {τ' : ∀ i, J' i → G i} (F' : GraphHom π τ' B B')
    (F : GraphHom π τ A B) :
    GraphHom π (J := fun i ↦ J i × J' i) (fun i p ↦ τ' i p.2 * τ i p.1) A B' :=
  ⟨fun i p ↦ (F'.f i p.2).comp (F.f i p.1), by
    simpa using F.tendsto.prodMul F'.tendsto (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)⟩

variable [IsIsometricSMul H X] [∀ i, Fintype (G i)] [∀ i, Fintype (J i)] [∀ i, Fintype (J' i)]

variable (π) in
/-- The shifted sum `∑_j F_j ⊗ R_{τ_j⁻¹}` as a chain map of `𝒜_G(X)`. -/
def toComplex (F : GraphHom π τ A B) : A.toComplex π ⟶ B.toComplex π where
  f r := graphHom π τ (fun i j ↦ (F.f i j).f) F.tendsto r r
  comm' r r' (h : r' + 1 = r) := by
    change graphHom π τ _ F.tendsto r r ≫ hom π (fun i ↦ (B.C i).d) B.tendsto_d r r' =
      hom π (fun i ↦ (A.C i).d) A.tendsto_d r r' ≫ graphHom π τ _ F.tendsto r' r'
    rw [graphHom_comp_hom _ _ _ fun i j κ σ hne hσ ↦ by have := (F.f i j).deg0 κ σ hne; omega,
      hom_comp_graphHom _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega]
    exact graphHom_congr rfl (funext₂ fun i j ↦ (F.f i j).comm) _ _ _ _

theorem toComplex_f (F : GraphHom π τ A B) (r : ℤ) :
    (F.toComplex π).f r = graphHom π τ (fun i j ↦ (F.f i j).f) F.tendsto r r := rfl

theorem toComplex_ofHom (F : Hom A B) :
    (ofHom (J := fun _ ↦ Unit) F).toComplex π = F.toComplex π := by
  ext r; exact (hom_eq_graphHom _ F.tendsto _ _).symm

theorem toComplex_add (F F' : GraphHom π τ A B) :
    (F.add F').toComplex π = F.toComplex π + F'.toComplex π := by
  ext r
  rw [HomologicalComplex.add_f_apply]
  exact (graphHom_add F.tendsto F'.tendsto _ _).symm

theorem toComplex_smul (c : ℚ) (F : GraphHom π τ A B) :
    (F.smul fun _ _ ↦ c).toComplex π = c • F.toComplex π := by
  ext r
  rw [HomologicalComplex.smul_f_apply]
  exact (graphHom_smul _ F.tendsto _ _).symm

theorem toComplex_comp {τ' : ∀ i, J' i → G i} (F' : GraphHom π τ' B B') (F : GraphHom π τ A B) :
    (F'.comp F).toComplex π = F.toComplex π ≫ F'.toComplex π := by
  ext r
  rw [HomologicalComplex.comp_f]
  exact (graphHom_comp F.tendsto F'.tendsto fun i j κ σ hne hσ ↦ by
    have := (F.f i j).deg0 κ σ hne; omega).symm

end GraphHom

variable [IsIsometricSMul H X] [∀ i, Fintype (G i)] [∀ i, Fintype (J i)]

variable {π} in
/-- A uniform family of exact homotopies as a mathlib `Homotopy` of the shifted sums. -/
def GraphHtpy.toHomotopy {F F' : GraphHom π τ A B} (K : GraphHtpy π F F') :
    Homotopy (F.toComplex π) (F'.toComplex π) where
  hom r r' := graphHom π τ (fun i j ↦ (K.h i j).h) K.tendsto r r'
  zero r r' h := graphHom_eq_zero _ fun i j κ σ hσ hκ ↦ by_contra fun hne ↦ h (by
    have := (K.h i j).deg1 κ σ hne; change r + 1 = r'; omega)
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    change graphHom π τ _ F.tendsto r r =
      hom π (fun i ↦ (A.C i).d) A.tendsto_d r (r - 1) ≫ graphHom π τ _ K.tendsto (r - 1) r +
        graphHom π τ _ K.tendsto r (r + 1) ≫ hom π (fun i ↦ (B.C i).d) B.tendsto_d (r + 1) r +
          graphHom π τ _ F'.tendsto r r
    rw [hom_comp_graphHom _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega,
      graphHom_comp_hom _ _ _ fun i j κ σ hne hσ ↦ by have := (K.h i j).deg1 κ σ hne; omega,
      graphHom_add, graphHom_add]
    refine graphHom_congr rfl (funext₂ fun i j ↦ ?_) _ _ _ _
    have := (K.h i j).eq
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel

/-! ### Chain maps and homotopies modulo the exterior `ℬ_{G,Z}(X)` -/

section Exterior

variable (Z : Set X) {u u' h : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ}

/-- The image of the complex of a controlled sequence in `ℬ_{G,Z}(X)`. -/
abbrev extComplex (A : ControlledSeq X) : ChainComplex (ExteriorCategory π Z) ℤ :=
  ((extFunctor π Z).mapHomologicalComplex _).obj (A.toComplex π)

/-- The commutator family `d u - u d` (the left sides of (9.5)). -/
def commFamily (u : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ) :
    ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ :=
  fun i j ↦ (B.C i).d * u i j - u i j * (A.C i).d

/-- The residual family `u - u' - (d h + h d)` (the left sides of (9.6)). -/
def htpyFamily (u u' h : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ) :
    ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ :=
  fun i j ↦ u i j - u' i j - ((B.C i).d * h i j + h i j * (A.C i).d)

variable {π Z}

omit [∀ i, Fintype (G i)] [∀ i, Fintype (J i)] in
theorem graphTendsto_commFamily
    (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label) :
    GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) (commFamily u) A.label B.label :=
  (hu.mul_left (B.tendsto_d.on _) (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)).sub
    (hu.mul_right (A.tendsto_d.on _) (Eventually.of_forall fun _ _ _ _ _ ↦ trivial))

omit [∀ i, Fintype (G i)] [∀ i, Fintype (J i)] in
theorem graphTendsto_htpyFamily
    (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label)
    (hu' : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u' A.label B.label)
    (hh : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) h A.label B.label) :
    GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) (htpyFamily u u' h) A.label B.label :=
  (hu.sub hu').sub ((hh.mul_left (B.tendsto_d.on _)
    (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)).add
      (hh.mul_right (A.tendsto_d.on _) (Eventually.of_forall fun _ _ _ _ _ ↦ trivial)))

variable (Z) in
/-- **Graph-type chain maps modulo the exterior** (§10): a family `u` of degree `0` and uniform
graph type whose commutators `d u - u d` have exterior witnesses after the sheet shift gives a
chain map `∑_j u_j ⊗ R_{τ_j⁻¹}` of `ℬ_{G,Z}(X)`, e.g. `E` of (10.2) from `A_g`. -/
def graphChainMap (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label)
    (hdeg : ∀ i j, HasDeg (A.C i) (B.C i) 0 (u i j))
    (hcomm : ∀ r, AsymptoticCategory.InIdeal Z (AsymptoticCategory.functor.map
      (graphHom π τ (commFamily u) (graphTendsto_commFamily hu) r (r - 1)))) :
    A.extComplex π Z ⟶ B.extComplex π Z :=
  chainMapOfMod (extFunctor π Z) (fun r ↦ graphHom π τ u hu r r) fun r r' (hr : r' + 1 = r) ↦ by
    obtain rfl : r' = r - 1 := by omega
    rw [extFunctor_map_eq_iff]
    convert hcomm r using 2
    change graphHom π τ u hu r r ≫ hom π (fun i ↦ (B.C i).d) B.tendsto_d r (r - 1) -
      hom π (fun i ↦ (A.C i).d) A.tendsto_d r (r - 1) ≫ graphHom π τ u hu (r - 1) (r - 1) = _
    rw [graphHom_comp_hom _ _ _ fun i j κ σ hne hσ ↦ by have := hdeg i j κ σ hne; omega,
      hom_comp_graphHom _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega,
      graphHom_sub]
    rfl

theorem graphChainMap_f (hu) (hdeg) (hcomm) (r : ℤ) :
    (graphChainMap (A := A) (B := B) Z hu hdeg hcomm).f r =
      (extFunctor π Z).map (graphHom π τ u hu r r) := rfl

/-- An honest graph-type chain map, pushed to `ℬ_{G,Z}(X)`. -/
theorem GraphHom.map_toComplex (F : GraphHom π τ A B) (hcomm) :
    ((extFunctor π Z).mapHomologicalComplex _).map (F.toComplex π) =
      graphChainMap Z F.tendsto (fun i j ↦ (F.f i j).deg0) hcomm := rfl

/-- **Graph-type homotopies modulo the exterior** (§10): if `u - u' - (dh + hd)` has exterior
witnesses after the sheet shift, the shifted sums are homotopic in `ℬ_{G,Z}(X)`, e.g. `E² ≃ E`
from `B̂_{g,h}`. -/
def graphHomotopy (hu hu') (hdeg hdeg') (hcomm hcomm')
    (hh : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) h A.label B.label)
    (hhdeg : ∀ i j, HasDeg (A.C i) (B.C i) 1 (h i j))
    (hres : ∀ r, AsymptoticCategory.InIdeal Z (AsymptoticCategory.functor.map
      (graphHom π τ (htpyFamily u u' h) (graphTendsto_htpyFamily hu hu' hh) r r))) :
    Homotopy (graphChainMap (A := A) (B := B) Z hu hdeg hcomm) (graphChainMap Z hu' hdeg' hcomm') :=
  homotopyOfMod _ _ _ (fun r r' ↦ graphHom π τ h hh r r')
    (fun r r' hr ↦ graphHom_eq_zero _ fun i j κ σ hσ hκ ↦ by_contra fun hne ↦ hr (by
      have := hhdeg i j κ σ hne; change r + 1 = r'; omega))
    fun r ↦ by
      rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
        prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp), extFunctor_map_eq_iff]
      convert hres r using 2
      change graphHom π τ u hu r r - (hom π (fun i ↦ (A.C i).d) A.tendsto_d r (r - 1) ≫
        graphHom π τ h hh (r - 1) r + graphHom π τ h hh r (r + 1) ≫
          hom π (fun i ↦ (B.C i).d) B.tendsto_d (r + 1) r + graphHom π τ u' hu' r r) = _
      rw [hom_comp_graphHom _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega,
        graphHom_comp_hom _ _ _ fun i j κ σ hne hσ ↦ by have := hhdeg i j κ σ hne; omega,
        graphHom_add, graphHom_add, graphHom_sub]
      refine graphHom_congr rfl (funext₂ fun i j ↦ ?_) _ _ _ _
      simp only [htpyFamily]; abel

/-- **Exterior witnesses**: a family whose nonzero entries have endpoints approaching an invariant
`Z` uniformly lies in `I_Z` after the sheet shift, however many terms it has. -/
theorem inIdeal_graphHom (hZ : ∀ h : H, h • Z = Z) (hu) {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hend : ∀ i j κ σ, u i j κ σ ≠ 0 →
      Metric.infEDist (B.label i κ) Z ≤ e i ∧ Metric.infEDist (A.label i σ) Z ≤ e i)
    (r r' : ℤ) :
    AsymptoticCategory.InIdeal Z (AsymptoticCategory.functor.map (graphHom π τ u hu r r')) :=
  inIdeal_graphSum hZ _ he fun i j _ _ hne ↦ hend i j _ _ hne

theorem extFunctor_map_graphHom_eq_zero (hZ : ∀ h : H, h • Z = Z) (hu) {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hend : ∀ i j κ σ, u i j κ σ ≠ 0 →
      Metric.infEDist (B.label i κ) Z ≤ e i ∧ Metric.infEDist (A.label i σ) Z ≤ e i)
    (r r' : ℤ) : (extFunctor π Z).map (graphHom π τ u hu r r') = 0 :=
  (extFunctor_map_eq_zero_iff _).mpr (inIdeal_graphHom hZ hu he hend r r')

end Exterior

end Families

end ControlledSeq

/-! ### Retained cells: the based section and projection of (9.1) -/

section Near

variable {α : Type*} [DecidableEq α] {P : α → Prop}

variable (P) in
/-- The based section `σ : C/F → C` of the retained cells `P` (9.1). -/
def nearIncl : Matrix α {a // P a} ℚ := Matrix.of fun ρ σ ↦ if σ.1 = ρ then 1 else 0

variable (P) in
/-- The based projection `π : C → C/F` onto the retained cells `P` (9.1). -/
def nearProj : Matrix {a // P a} α ℚ := Matrix.of fun σ ρ ↦ if σ.1 = ρ then 1 else 0

theorem nearIncl_ne_zero {ρ : α} {σ : {a // P a}} (h : nearIncl P ρ σ ≠ 0) : σ.1 = ρ := by
  by_contra h'; simp [nearIncl, h'] at h

theorem nearProj_ne_zero {ρ : α} {σ : {a // P a}} (h : nearProj P σ ρ ≠ 0) : σ.1 = ρ := by
  by_contra h'; simp [nearProj, h'] at h

theorem nearProj_mul [Fintype α] {β : Type*} (u : Matrix α β ℚ) :
    nearProj P * u = u.submatrix Subtype.val id := by
  ext σ b; simp [nearProj, mul_apply]

theorem mul_nearIncl [Fintype α] {β : Type*} (u : Matrix β α ℚ) :
    u * nearIncl P = u.submatrix id Subtype.val := by
  ext b σ; simp [nearIncl, mul_apply]

/-- `π u σ` is the restriction of `u` to the retained cells. -/
theorem nearProj_mul_mul_nearIncl [Fintype α] {β : Type*} [DecidableEq β] [Fintype β]
    {Q : β → Prop} (u : Matrix α β ℚ) :
    nearProj P * u * nearIncl Q = u.submatrix Subtype.val Subtype.val := by
  rw [nearProj_mul, mul_nearIncl]; rfl

/-- `πσ = 1`. -/
theorem nearProj_mul_nearIncl [Fintype α] : nearProj P * nearIncl P = 1 := by
  rw [nearProj_mul]
  ext σ σ'
  simp [nearIncl, one_apply, Subtype.ext_iff, eq_comm]

theorem nearIncl_mul_nearProj_apply [DecidablePred P] [Fintype {a // P a}] (ρ ρ' : α) :
    (nearIncl P * nearProj P) ρ ρ' = if P ρ ∧ ρ = ρ' then 1 else 0 := by
  rw [mul_apply]
  by_cases hρ : P ρ
  · rw [Finset.sum_eq_single ⟨ρ, hρ⟩ (fun σ _ hσ ↦ ?_) (by simp)]
    · by_cases h : ρ = ρ'
      · subst h; simp [nearIncl, nearProj, hρ]
      · simp [nearIncl, nearProj, h]
    · have : σ.1 ≠ ρ := fun h ↦ hσ (Subtype.ext h)
      simp [nearIncl, this]
  · rw [Finset.sum_eq_zero fun σ _ ↦ ?_]
    · simp [hρ]
    · have : σ.1 ≠ ρ := fun h ↦ hρ (h ▸ σ.2)
      simp [nearIncl, this]

/-- `P = 1 - σπ` is the diagonal far projection of Lemma 9.1. -/
theorem one_sub_nearIncl_mul_nearProj [Fintype α] (far : α → Prop) [DecidablePred far] :
    1 - nearIncl (fun a ↦ ¬far a) * nearProj (fun a ↦ ¬far a) = farProj far := by
  ext ρ ρ'
  rw [Matrix.sub_apply, nearIncl_mul_nearProj_apply]
  by_cases h : ρ = ρ'
  · subst h; by_cases hf : far ρ <;> simp [farProj, hf]
  · simp [farProj, h]

variable {Y : Type*} [PseudoEMetricSpace Y]

theorem prop_nearIncl (ℓ : α → Y) : prop (nearIncl P) (fun σ ↦ ℓ σ.1) ℓ = 0 :=
  le_antisymm (prop_le_iff.mpr fun ρ σ h ↦ by obtain rfl := nearIncl_ne_zero h; simp) bot_le

theorem prop_nearProj (ℓ : α → Y) : prop (nearProj P) ℓ (fun σ ↦ ℓ σ.1) = 0 :=
  le_antisymm (prop_le_iff.mpr fun σ ρ h ↦ by obtain rfl := nearProj_ne_zero h; simp) bot_le

theorem prop_farProj [Fintype α] (far : α → Prop) (ℓ : α → Y) : prop (farProj far) ℓ ℓ = 0 := by
  rw [farProj]; convert prop_diagonal _ ℓ

end Near

/-- The restriction `π u σ` of a matrix to the retained cells (9.3). -/
abbrev nearMat {α β : Type*} (P : α → Prop) (Q : β → Prop) (u : Matrix α β ℚ) :
    Matrix {a // P a} {b // Q b} ℚ :=
  u.submatrix Subtype.val Subtype.val

/-! ### The compression identities (9.4)–(9.6) for based matrices -/

section CompressMat

variable {C C' C'' : BasedComplex} {far : C.X → Prop} {far' : C'.X → Prop}
  {far'' : C''.X → Prop} [DecidablePred far] [DecidablePred far'] [DecidablePred far'']

/-- `π d P = 0` (l.719): the far cells form a subcomplex. -/
theorem nearProj_mul_d_mul_farProj (hfar : C.IsSub far) :
    nearProj (fun σ ↦ ¬far σ) * C.d * farProj far = 0 := by
  ext σ ρ
  simp only [nearProj_mul, farProj, mul_diagonal, submatrix_apply, id, Matrix.zero_apply]
  by_cases hρ : far ρ
  · rw [ite_eq_left hρ, mul_one]
    by_contra h
    exact σ.2 (hfar σ.1 ρ h hρ)
  · rw [ite_eq_right hρ, mul_zero]

theorem nearMat_d_mul_farProj_mul (hfar : C.IsSub far) {β : Type*} [DecidableEq β] [Fintype β]
    {Q : β → Prop} (u : Matrix C.X β ℚ) :
    nearMat (fun σ ↦ ¬far σ) Q (C.d * (farProj far * u)) = 0 := by
  rw [nearMat, ← nearProj_mul_mul_nearIncl, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    nearProj_mul_d_mul_farProj hfar, Matrix.zero_mul, Matrix.zero_mul]

omit [DecidablePred far] [DecidablePred far''] in
/-- **(9.4)**: `(v u)^ = v̂ û + π v P u σ`. -/
theorem nearMat_mul (u : Matrix C'.X C.X ℚ) (v : Matrix C''.X C'.X ℚ) :
    nearMat (fun σ ↦ ¬far'' σ) (fun σ ↦ ¬far σ) (v * u) =
      nearMat (fun σ ↦ ¬far'' σ) (fun σ ↦ ¬far' σ) v *
          nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) u +
        nearMat (fun σ ↦ ¬far'' σ) (fun σ ↦ ¬far σ) (v * (farProj far' * u)) := by
  have h := one_sub_nearIncl_mul_nearProj far'
  simp only [nearMat, ← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far'' σ)
    (Q := fun σ ↦ ¬far σ), ← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far'' σ)
    (Q := fun σ ↦ ¬far' σ), ← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far' σ)
    (Q := fun σ ↦ ¬far σ), ← h]
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  abel

/-- **(9.5)**: for a chain map `a`, `d̂ â - â d̂ = π a P d σ`. -/
theorem nearMat_comm (hfar' : C'.IsSub far') (a : Hom C C') :
    nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far' σ) C'.d *
          nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) a.f -
        nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) a.f *
          nearMat (fun σ ↦ ¬far σ) (fun σ ↦ ¬far σ) C.d =
      nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) (a.f * (farProj far * C.d)) := by
  have h₁ := nearMat_mul (far := far) (far' := far') (far'' := far') a.f C'.d
  have h₂ := nearMat_mul (far := far) (far' := far) (far'' := far') C.d a.f
  rw [nearMat_d_mul_farProj_mul hfar', add_zero, a.comm] at h₁
  rw [← h₁, h₂]
  abel

/-- **(9.6)**, homotopy part: from `f - g = d H + H d`, `f̂ - ĝ - (d̂ Ĥ + Ĥ d̂) = π H P d σ`. -/
theorem nearMat_htpy (hfar' : C'.IsSub far') {f g : Hom C C'} (H : Htpy f g) :
    nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) f.f -
        nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) g.f -
        (nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far' σ) C'.d *
            nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) H.h +
          nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) H.h *
            nearMat (fun σ ↦ ¬far σ) (fun σ ↦ ¬far σ) C.d) =
      nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) (H.h * (farProj far * C.d)) := by
  have h₁ := nearMat_mul (far := far) (far' := far') (far'' := far') H.h C'.d
  have h₂ := nearMat_mul (far := far) (far' := far) (far'' := far') C.d H.h
  rw [nearMat_d_mul_farProj_mul hfar', add_zero] at h₁
  have hH : f.f - g.f = C'.d * H.h + H.h * C.d := H.eq
  rw [← h₁, ← sub_eq_zero]
  have : nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) f.f -
      nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) g.f =
      nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) (C'.d * H.h) +
        nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ) (H.h * C.d) :=
    congrArg (nearMat (fun σ ↦ ¬far' σ) (fun σ ↦ ¬far σ)) hH
  rw [this, h₂]
  abel

end CompressMat

/-! ### Carrier-defined far subcomplexes (l.710) -/

namespace Geometry

variable {C : BasedComplex} {E : Type*} (g : Geometry C E) (K : Set E)

/-- The far cells of l.710: closed carriers missing `K`, e.g. `K = f⁻¹(B̄(y,t))`.  Unlike a
threshold on labels, this is a subcomplex (`isSub_carrierFar`). -/
def carrierFar (σ : C.X) : Prop := Disjoint (g.carrier σ) K

theorem isSub_carrierFar : C.IsSub (g.carrierFar K) :=
  fun σ τ h hτ ↦ hτ.mono_left (g.face_sub σ τ h)

variable {g K}

theorem center_notMem_of_carrierFar {σ : C.X} (h : g.carrierFar K σ) : g.center σ ∉ K :=
  Set.disjoint_left.mp h (g.center_mem σ)

variable {Y : Type*} [PseudoMetricSpace Y] {lab : E → Y} {y : Y} {t : ℝ}

/-- Far cells are labelled beyond `t` (the hypothesis on `far` in Lemma 9.1). -/
theorem lt_dist_of_carrierFar (hK : lab ⁻¹' Metric.closedBall y t ⊆ K) {σ : C.X}
    (h : g.carrierFar K σ) : t < dist (lab (g.center σ)) y :=
  lt_of_not_ge fun h' ↦ center_notMem_of_carrierFar h (hK h')

/-- Retained cells are labelled within `t + κ` if the label oscillates by at most `κ` on their
carriers (the bound `t + κ_i` of §9, l.721). -/
theorem dist_le_of_not_carrierFar (hK : K ⊆ lab ⁻¹' Metric.closedBall y t) {σ : C.X} {κ : ℝ}
    (hosc : ∀ x ∈ g.carrier σ, dist (lab (g.center σ)) (lab x) ≤ κ) (h : ¬g.carrierFar K σ) :
    dist (lab (g.center σ)) y ≤ t + κ := by
  obtain ⟨x, hx, hxK⟩ := Set.not_disjoint_iff.mp h
  calc dist (lab (g.center σ)) y ≤ dist (lab (g.center σ)) (lab x) + dist (lab x) y :=
        dist_triangle _ _ _
    _ ≤ κ + t := add_le_add (hosc x hx) (hK hxK)
    _ = t + κ := add_comm _ _

end Geometry

namespace ControlledSeq

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Compression `C_i = D_i/F_i` of a controlled sequence -/

/-- **Compression** `C_i = D_i/F_i` of (9.1) by far subcomplexes `F_i`, labelled on the retained
cells.  The differential need only be controlled on buffers that eventually contain the
retained cells (§9, l.721), as for the `(ρ̃, f)`-labels of `D_i`. -/
def quotOfBuffer (D : ℕ → BasedComplex) (label : ∀ i, (D i).X → X) (buf : ∀ i, (D i).X → Prop)
    (far : ∀ i, (D i).X → Prop) [∀ i, DecidablePred (far i)] (hfar : ∀ i, (D i).IsSub (far i))
    (hd : PropTendstoOn buf (fun i ↦ (D i).d) label label)
    (hnear : ∀ᶠ i in atTop, ∀ σ, ¬far i σ → buf i σ) : ControlledSeq X where
  C i := (D i).restrict (fun σ ↦ ¬far i σ) (hfar i).isLocallyClosed_compl
  label i σ := label i σ.1
  tendsto_d := hd.restrict (fun _ ↦ Subtype.val) (fun _ ↦ Subtype.val)
    (hnear.mono fun _ h σ ↦ h σ.1 σ.2)

/-- The compression of an honest controlled sequence. -/
def quot (D : ControlledSeq X) (far : ∀ i, (D.C i).X → Prop) [∀ i, DecidablePred (far i)]
    (hfar : ∀ i, (D.C i).IsSub (far i)) : ControlledSeq X :=
  quotOfBuffer D.C D.label (fun _ _ ↦ True) far hfar (D.tendsto_d.on _)
    (Eventually.of_forall fun _ _ _ ↦ trivial)

/-- The same complexes with new labels. -/
def relabel {Y : Type*} [PseudoEMetricSpace Y] (A : ControlledSeq X) (ℓ : ∀ i, (A.C i).X → Y)
    (h : PropTendsto (fun i ↦ (A.C i).d) ℓ ℓ) : ControlledSeq Y :=
  ⟨A.C, ℓ, h⟩

/-- The buffered compression is the honest one, relabelled: identities of compressed matrices
proved in the `f`-labels transfer to the `(ρ̃, f)`-labels (`graphHom_relabel`). -/
theorem quotOfBuffer_eq_relabel (D : ControlledSeq X) {Y : Type*} [PseudoEMetricSpace Y]
    (ℓ : ∀ i, (D.C i).X → Y) (buf : ∀ i, (D.C i).X → Prop) (far : ∀ i, (D.C i).X → Prop)
    [∀ i, DecidablePred (far i)] (hfar : ∀ i, (D.C i).IsSub (far i)) (hd) (hnear) :
    quotOfBuffer D.C ℓ buf far hfar hd hnear =
      (D.quot far hfar).relabel (fun i σ ↦ ℓ i σ.1)
        (quotOfBuffer D.C ℓ buf far hfar hd hnear).tendsto_d :=
  rfl

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] {π : ∀ i, G i →* H}
  [MulAction H X] {J J' : ℕ → Type*} {τ : ∀ i, J i → G i}

/-- **Buffered graph type becomes honest after compression** (§9, l.721): on the retained
cells, eventually inside the buffers, the compressed matrices `π u σ` have graph type. -/
theorem _root_.HSFormal.GraphTendsto.quotOfBuffer {D D' : ℕ → BasedComplex} {ℓ : ∀ i, (D i).X → X}
    {ℓ' : ∀ i, (D' i).X → X} {buf : ∀ i, (D i).X → Prop} {buf' : ∀ i, (D' i).X → Prop}
    {far : ∀ i, (D i).X → Prop} {far' : ∀ i, (D' i).X → Prop} [∀ i, DecidablePred (far i)]
    [∀ i, DecidablePred (far' i)] {hfar : ∀ i, (D i).IsSub (far i)}
    {hfar' : ∀ i, (D' i).IsSub (far' i)} {hd hnear hd' hnear'} {θ : ∀ i, J i → H}
    {u : ∀ i, J i → Matrix (D' i).X (D i).X ℚ} (hu : GraphTendsto buf θ u ℓ ℓ') :
    GraphTendsto (fun _ _ ↦ True) θ (fun i j ↦ (u i j).submatrix Subtype.val Subtype.val)
      (quotOfBuffer D ℓ buf far hfar hd hnear).label
      (quotOfBuffer D' ℓ' buf' far' hfar' hd' hnear').label :=
  hu.restrict _ _ (hnear.mono fun _ h σ ↦ h σ.1 σ.2)

section QuotFamilies

variable {D D' D'' : ℕ → BasedComplex} {ℓ : ∀ i, (D i).X → X} {ℓ' : ∀ i, (D' i).X → X}
  {ℓ'' : ∀ i, (D'' i).X → X} {buf : ∀ i, (D i).X → Prop} {buf' : ∀ i, (D' i).X → Prop}
  {buf'' : ∀ i, (D'' i).X → Prop} {far : ∀ i, (D i).X → Prop} {far' : ∀ i, (D' i).X → Prop}
  {far'' : ∀ i, (D'' i).X → Prop} [∀ i, DecidablePred (far i)] [∀ i, DecidablePred (far' i)]
  [∀ i, DecidablePred (far'' i)] {hfar : ∀ i, (D i).IsSub (far i)}
  {hfar' : ∀ i, (D' i).IsSub (far' i)} {hfar'' : ∀ i, (D'' i).IsSub (far'' i)}
  {hd hnear hd' hnear' hd'' hnear''}

/-- **(9.5) for compressed families**: the commutators of `Â = π a σ` with `d̂` are the words
`π a P d σ`, which factor through the reachable band (Lemma 9.1). -/
theorem commFamily_quotOfBuffer (a : ∀ i, J i → BasedComplex.Hom (D i) (D' i)) :
    commFamily (A := quotOfBuffer D ℓ buf far hfar hd hnear)
        (B := quotOfBuffer D' ℓ' buf' far' hfar' hd' hnear')
        (fun i j ↦ nearMat (fun σ ↦ ¬far' i σ) (fun σ ↦ ¬far i σ) (a i j).f) =
      fun i j ↦ nearMat (fun σ ↦ ¬far' i σ) (fun σ ↦ ¬far i σ)
        ((a i j).f * (farProj (far i) * (D i).d)) :=
  funext₂ fun i j ↦ nearMat_comm (hfar' i) (a i j)

/-- **(9.6) for compressed families**: from `a'a - b = dB + Bd` (8.5),
`Â'Â - B̂ - (d̂B̂ + B̂d̂) = π B P d σ - π a' P a σ`. -/
theorem htpyFamily_quotOfBuffer (a : ∀ i, J i → BasedComplex.Hom (D i) (D' i))
    (a' : ∀ i, J i → BasedComplex.Hom (D' i) (D'' i))
    (b : ∀ i, J i → BasedComplex.Hom (D i) (D'' i))
    (B : ∀ i j, BasedComplex.Htpy ((a' i j).comp (a i j)) (b i j)) :
    htpyFamily (A := quotOfBuffer D ℓ buf far hfar hd hnear)
        (B := quotOfBuffer D'' ℓ'' buf'' far'' hfar'' hd'' hnear'')
        (fun i j ↦ nearMat (fun σ ↦ ¬far'' i σ) (fun σ ↦ ¬far' i σ) (a' i j).f *
          nearMat (fun σ ↦ ¬far' i σ) (fun σ ↦ ¬far i σ) (a i j).f)
        (fun i j ↦ nearMat (fun σ ↦ ¬far'' i σ) (fun σ ↦ ¬far i σ) (b i j).f)
        (fun i j ↦ nearMat (fun σ ↦ ¬far'' i σ) (fun σ ↦ ¬far i σ) (B i j).h) =
      fun i j ↦ nearMat (fun σ ↦ ¬far'' i σ) (fun σ ↦ ¬far i σ)
          ((B i j).h * (farProj (far i) * (D i).d)) -
        nearMat (fun σ ↦ ¬far'' i σ) (fun σ ↦ ¬far i σ)
          ((a' i j).f * (farProj (far' i) * (a i j).f)) :=
  funext₂ fun i j ↦ by
    have h := nearMat_htpy (far := far i) (hfar'' i) (B i j)
    have hm := nearMat_mul (far := far i) (far' := far' i) (far'' := far'' i) (a i j).f (a' i j).f
    rw [Hom.comp_f] at h
    rw [hm] at h
    rw [← h]
    simp only [htpyFamily]
    abel

end QuotFamilies

variable [IsIsometricSMul H X] [∀ i, Fintype (G i)] [∀ i, Fintype (J i)]

/-- **Transfer between labellings**: shifted families are label-independent matrices, so an
identity proved over one labelling of the complexes holds over any other. -/
theorem graphHom_relabel {A B : ControlledSeq X} {Y : Type*} [PseudoEMetricSpace Y]
    [MulAction H Y] [IsIsometricSMul H Y] {ℓA : ∀ i, (A.C i).X → Y} {ℓB : ∀ i, (B.C i).X → Y}
    {hA hB}
    {J₁ J₂ : ℕ → Type*} [∀ i, Fintype (J₁ i)] [∀ i, Fintype (J₂ i)] {τ₁ : ∀ i, J₁ i → G i}
    {τ₂ : ∀ i, J₂ i → G i} {u : ∀ i, J₁ i → Matrix (B.C i).X (A.C i).X ℚ}
    {v : ∀ i, J₂ i → Matrix (B.C i).X (A.C i).X ℚ} {hu hv hu' hv'} {r r' : ℤ}
    (h : graphHom π τ₁ u hu r r' = graphHom π τ₂ v hv r r') :
    graphHom π (A := A.relabel ℓA hA) (B := B.relabel ℓB hB) τ₁ u hu' r r' =
      graphHom π (A := A.relabel ℓA hA) (B := B.relabel ℓB hB) τ₂ v hv' r r' :=
  hom_ext fun i ↦ by
    have := congrArg (fun φ ↦ φ.1 i) h
    simp only [graphHom_val] at this ⊢
    exact this

/-! ### The near part in `𝒜_G(X)` -/

section NearPart

variable (π) (D : ControlledSeq X) (far : ∀ i, (D.C i).X → Prop) [∀ i, DecidablePred (far i)]
  (hfar : ∀ i, (D.C i).IsSub (far i))

/-- The quotient chain map `π : D → D/F`, controlled since `F` is a subcomplex. -/
def toQuot : Hom D (D.quot far hfar) :=
  ⟨fun i ↦ projHom (hfar i), tendsto_zero_of_forall_eq_zero fun _ ↦ prop_nearProj _⟩

theorem tendsto_nearIncl :
    PropTendsto (C := (D.quot far hfar).C) (D := D.C) (fun i ↦ nearIncl fun σ ↦ ¬far i σ)
      (D.quot far hfar).label D.label :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_nearIncl _

/-- **The near part** `(σ, π)` of `D` in `𝒜_G(X)`: degreewise retracts onto the retained
cells of the far subcomplexes `F_i` (9.1). -/
def nearPart : Compression.NearPart (fun r ↦ (D.quot far hfar).obj π r) (D.toComplex π) :=
  fun r ↦
    { i := hom π (A := D.quot far hfar) (B := D) (fun i ↦ nearIncl fun σ ↦ ¬far i σ)
        (tendsto_nearIncl D far hfar) r r
      r := ((D.toQuot far hfar).toComplex π).f r
      retract := by
        erw [Hom.toComplex_f, hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
          rw [← nearIncl_ne_zero h]; exact hσ]
        exact (hom_congr (funext fun _ ↦ nearProj_mul_nearIncl) _ _ _ _).trans hom_one }

theorem nearPart_i (r : ℤ) :
    (nearPart π D far hfar r).i = hom π (A := D.quot far hfar) (B := D)
      (fun i ↦ nearIncl fun σ ↦ ¬far i σ) (tendsto_nearIncl D far hfar) r r := rfl

theorem nearPart_r (r : ℤ) :
    (nearPart π D far hfar r).r = hom π (A := D) (B := D.quot far hfar)
      (fun i ↦ nearProj fun σ ↦ ¬far i σ) (D.toQuot far hfar).tendsto r r := rfl

/-- `πdP = 0` (l.719): the far part is a subcomplex. -/
theorem farClosed_nearPart : Compression.FarClosed (nearPart π D far hfar) :=
  Compression.farClosed_of_hom (C := (D.quot far hfar).toComplex π) _
    ((D.toQuot far hfar).toComplex π) fun _ ↦ rfl

/-- The compressed complex `(C, d̂)` of Compression is the complex of the compression. -/
theorem compressed_nearPart :
    Compression.compressed (nearPart π D far hfar) (.inl (farClosed_nearPart π D far hfar)) =
      (D.quot far hfar).toComplex π :=
  HomologicalComplex.ext rfl fun r r' _ ↦
    (Category.comp_id _).trans ((Compression.hatD_eq_of_hom (C := (D.quot far hfar).toComplex π)
      (nearPart π D far hfar) ((D.toQuot far hfar).toComplex π) (fun _ ↦ rfl) r r').trans
        (Category.id_comp _).symm)

theorem quotientMap_nearPart_f (r : ℤ) :
    (Compression.quotientMap (nearPart π D far hfar) (farClosed_nearPart π D far hfar)).f r =
      ((D.toQuot far hfar).toComplex π).f r := rfl

theorem hom_sub {A B : ControlledSeq X} (u v : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu hv)
    (r r' : ℤ) : hom π u hu r r' - hom π v hv r r' = hom π (fun i ↦ u i - v i) (hu.sub hv) r r' :=
  hom_ext fun i ↦ by simp only [sub_val, hom_val, ← sheet_sub]; rfl

omit [∀ i, DecidablePred (far i)] in
theorem tendsto_farProj : PropTendsto (fun i ↦ farProj (far i)) D.label D.label :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_farProj _ _

/-- The far projection `P = 1 - σπ` is the diagonal projection onto the far cells. -/
theorem far_nearPart (r : ℤ) :
    Compression.far (nearPart π D far hfar r) =
      hom π (fun i ↦ farProj (far i)) (tendsto_farProj D far) r r := by
  rw [Compression.far, nearPart_i, nearPart_r]
  erw [hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
    obtain rfl := nearProj_ne_zero h; exact hσ]
  refine (congrArg (· - _) (hom_one (A := D) (π := π) (r := r)).symm).trans ?_
  rw [hom_sub]
  exact hom_congr (funext fun _ ↦ one_sub_nearIncl_mul_nearProj _) _ _ _ _

section Compress

variable {D D' D'' : ControlledSeq X} {far : ∀ i, (D.C i).X → Prop}
  {far' : ∀ i, (D'.C i).X → Prop} {far'' : ∀ i, (D''.C i).X → Prop} [∀ i, DecidablePred (far i)]
  [∀ i, DecidablePred (far' i)] [∀ i, DecidablePred (far'' i)] {hfar : ∀ i, (D.C i).IsSub (far i)}
  {hfar' : ∀ i, (D'.C i).IsSub (far' i)} {hfar'' : ∀ i, (D''.C i).IsSub (far'' i)}
  [∀ i, Fintype (J' i)] {τ' : ∀ i, J' i → G i}

/-- **Compression of shifted families** (9.3): `π (∑_j u_j ⊗ R_{τ_j⁻¹}) σ` is the shifted sum of
the restrictions `π u_j σ` to the retained cells. -/
theorem compress_graphHom (u : ∀ i, J i → Matrix (D'.C i).X (D.C i).X ℚ) (hu) {r r' : ℤ}
    (hdeg : ∀ i j κ σ, u i j κ σ ≠ 0 → (D.C i).deg σ = r → (D'.C i).deg κ = r') :
    Compression.compress (nearPart π D far hfar r) (nearPart π D' far' hfar' r')
        (graphHom π τ u hu r r') =
      graphHom π (A := D.quot far hfar) (B := D'.quot far' hfar') τ
        (fun i j ↦ (u i j).submatrix Subtype.val Subtype.val)
        (hu.restrict _ _ (Eventually.of_forall fun _ _ ↦ trivial)) r r' := by
  rw [Compression.compress, nearPart_i, nearPart_r]
  erw [graphHom_comp_hom _ _ _ hdeg,
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by obtain rfl := nearIncl_ne_zero h; exact hσ]
  exact graphHom_congr rfl (funext₂ fun _ _ ↦ nearProj_mul_mul_nearIncl _) _ _ _ _

theorem farProj_ne_zero {α : Type*} [Fintype α] {far : α → Prop} {κ σ : α}
    (h : farProj far κ σ ≠ 0) : κ = σ := by
  by_contra h'; exact h (by simp [farProj, h'])

/-- **Residual words through the far projection** (Lemma 9.1): the word `σ u P v π` of
Compression's formulas is the shifted sum of the restricted matrices `π v P u σ`, over all pairs
of sheets, with types `τ' τ`. -/
theorem nearPart_word (u : ∀ i, J i → Matrix (D'.C i).X (D.C i).X ℚ)
    (v : ∀ i, J' i → Matrix (D''.C i).X (D'.C i).X ℚ) (hu hv) {r r' r'' : ℤ}
    (hdu : ∀ i j κ σ, u i j κ σ ≠ 0 → (D.C i).deg σ = r → (D'.C i).deg κ = r')
    (hdv : ∀ i j κ σ, v i j κ σ ≠ 0 → (D'.C i).deg σ = r' → (D''.C i).deg κ = r'') :
    (nearPart π D far hfar r).i ≫ graphHom π τ u hu r r' ≫
        Compression.far (nearPart π D' far' hfar' r') ≫ graphHom π τ' v hv r' r'' ≫
          (nearPart π D'' far'' hfar'' r'').r =
      graphHom π (A := D.quot far hfar) (B := D''.quot far'' hfar'') (J := fun i ↦ J i × J' i)
        (fun i p ↦ τ' i p.2 * τ i p.1)
        (fun i p ↦ (v i p.2 * (farProj (far' i) * u i p.1)).submatrix Subtype.val Subtype.val)
        (by simp only [map_mul]
            exact ((hu.mul_left ((tendsto_farProj D' far').on fun _ _ ↦ True)
          (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)).prodMul hv
            (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)).restrict
              (fun _ ↦ Subtype.val) (fun _ ↦ Subtype.val)
                (Eventually.of_forall fun _ _ ↦ trivial)) r r'' := by
  rw [far_nearPart, nearPart_i, nearPart_r]
  erw [graphHom_comp_hom _ _ _ hdv,
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by rw [farProj_ne_zero h]; exact hσ,
    graphHom_comp _ _ hdu,
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by obtain rfl := nearIncl_ne_zero h; exact hσ]
  refine graphHom_congr rfl (funext₂ fun i p ↦ ?_) _ _ _ _
  erw [← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far'' i σ) (Q := fun σ ↦ ¬far i σ)]
  simp only [Matrix.mul_assoc]
  repeat erw [Matrix.mul_assoc]

/-- `nearPart_word` with a first factor of type `1`, e.g. `π a P d σ` of (9.5). -/
theorem nearPart_word_hom (u : ∀ i, Matrix (D'.C i).X (D.C i).X ℚ) (hu : PropTendsto u _ _)
    (v : ∀ i, J' i → Matrix (D''.C i).X (D'.C i).X ℚ) (hv) {r r' r'' : ℤ}
    (hdu : ∀ i κ σ, u i κ σ ≠ 0 → (D.C i).deg σ = r → (D'.C i).deg κ = r')
    (hdv : ∀ i j κ σ, v i j κ σ ≠ 0 → (D'.C i).deg σ = r' → (D''.C i).deg κ = r'') :
    (nearPart π D far hfar r).i ≫ hom π u hu r r' ≫
        Compression.far (nearPart π D' far' hfar' r') ≫ graphHom π τ' v hv r' r'' ≫
          (nearPart π D'' far'' hfar'' r'').r =
      graphHom π (A := D.quot far hfar) (B := D''.quot far'' hfar'') τ'
        (fun i j ↦ (v i j * (farProj (far' i) * u i)).submatrix Subtype.val Subtype.val)
        ((hv.mul_right (((tendsto_farProj D' far').mul hu).on fun _ _ ↦ True)
          (Eventually.of_forall fun _ _ _ _ _ ↦ trivial)).restrict
            (fun _ ↦ Subtype.val) (fun _ ↦ Subtype.val) (Eventually.of_forall fun _ _ ↦ trivial))
        r r'' := by
  rw [far_nearPart, nearPart_i, nearPart_r]
  erw [graphHom_comp_hom _ _ _ hdv,
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by rw [farProj_ne_zero h]; exact hσ,
    hom_comp_graphHom _ _ _ hdu,
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by obtain rfl := nearIncl_ne_zero h; exact hσ]
  refine graphHom_congr rfl (funext₂ fun i j ↦ ?_) _ _ _ _
  erw [← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far'' i σ) (Q := fun σ ↦ ¬far i σ)]
  simp only [Matrix.mul_assoc]
  repeat erw [Matrix.mul_assoc]

end Compress

end NearPart

/-! ### Free sheets (l.849) -/

section FreeSheet

variable {A B : ControlledSeq X}

variable (π) in
/-- The free-sheet functor copies the one-sheet matrices of a controlled sequence. -/
theorem freeSheet_map_hom (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) (r r' : ℤ) :
    (AsymptoticObject.freeSheet π).map (hom (scalarHom H) u hu r r') = hom π u hu r r' :=
  hom_ext fun i ↦ by
    rw [freeSheet_map, sheetHom_val, hom_val]
    congr 1
    ext k' k
    simp [scalarMatrix, hom_val, sheet_apply, block]

variable (π) in
/-- `Ind`: the free sheets over the scalar complex of a controlled sequence are its complex in
`𝒜_G(X)` (§10, (10.1)). -/
theorem freeSheet_toComplex (A : ControlledSeq X) :
    ((AsymptoticObject.freeSheet π).mapHomologicalComplex _).obj (A.toComplex (scalarHom H)) =
      A.toComplex π :=
  HomologicalComplex.ext rfl fun r r' _ ↦
    (Category.comp_id _).trans ((freeSheet_map_hom π (fun i ↦ (A.C i).d) A.tendsto_d r r').trans
      (Category.id_comp _).symm)

variable (π) in
/-- `Ind` in the exterior quotient: `ℬ_{1,Z} → ℬ_{G,Z}` sends the scalar complex of `A` to its
complex in `ℬ_{G,Z}(X)`, on which the shifted graph-type families act. -/
theorem exteriorFreeSheet_extComplex {Z : Set X} (hZ : ∀ h : H, h • Z = Z) (A : ControlledSeq X) :
    ((ExteriorCategory.freeSheet π hZ).mapHomologicalComplex _).obj
        (A.extComplex (scalarHom H) Z) = A.extComplex π Z :=
  HomologicalComplex.ext rfl fun r r' _ ↦
    (Category.comp_id _).trans ((congrArg (fun f ↦ (extFunctor π Z).map f)
      (freeSheet_map_hom π (fun i ↦ (A.C i).d) A.tendsto_d r r')).trans (Category.id_comp _).symm)

end FreeSheet

end ControlledSeq

end BasedComplex

end HSFormal.Cubical
