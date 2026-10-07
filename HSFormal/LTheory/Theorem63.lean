import HSFormal.LTheory.LocalizationSupport
import HSFormal.LTheory.TailSignature
import HSFormal.Bridges

/-!
# Theorem 6.3 on `L`, the iterated boundaries `Δ_T`, `Δ_1` and `TransferDivisibility`

Assembly steps S7–S9, S12b (manuscript §4 l.181–240, §6 l.398–455, §11 l.883–912, §12).

* (a) **Theorem 6.3.** `exists_trivializingCover`: a compact metric space with a free isometric
  action of a finite group has a finite closed invariant cover by pieces lying in the translates
  of an open set with disjoint translates (the hypotheses of `lemma_6_2`).
  `forgetControl_comp_tensor`: `τ ⊗ −` commutes with forgetting control.
  `σtail_forgetControl_liftPred_dvd` (general free action of a group of prime order) and
  `theorem_6_3` (the free `C_p`-sphere `T` of `ControlData` with `TailGroups`):
  `σ_tail(forgetControl α) ∈ divTail p` for every `α ∈ L_4(𝒜_G(T))`.
* (b) **The iterated boundary (11.1).** `CutFlag`: the cut data (exterior cut (4.2), hemisphere
  cuts (4.1), positive component of `S⁰`); `CutFlag.delta = projSep ∘ iterDown mvCut ∘ cut`.
  `ControlData.flag`: the cuts fixed by `cd` (ball `B̄(y, r)`, closed hemispheres in the ambient
  coordinates of `Sⁿ ⊂ ℝⁿ⁺¹`, positive point of `S⁰`); `CutFlag.lift`: the same cuts on `T × Sⁿ`.
  `ControlData.deltaT`, `ControlData.delta1`; `fibreSignature 𝕃 = σ_tail ∘ Δ_1 ∘ 𝕃.cls`
  (`fibreSignatureOf` for any `FlagChoice`).
* (c) **(11.2) and `TransferDivisibility`.** `SupportHom` (functors carrying supports along a map
  `j`), with naturality of every cut: `mvBdryOf_natural`, `mvBdry41_natural`, `projSep_natural`,
  `cutBdry_natural`, `CutFlag.delta_natural`; `ControlData.toPoint_deltaT` is (11.2)
  `U₄ ∘ Δ_T = Δ_1 ∘ U`; `transferDivisibility_of`, `transferDivisibility`.

Identities between functors of different full subcategories are proved for abstract filtrations
(`subMap_comp_filtSub`, `restrictSubIso_comp_filtSub`) and instantiated: by `rfl` on the concrete
support categories the kernel unfolds them expensively.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Filter Topology Metric AsymptoticCategory AsymptoticObject
open scoped Pointwise

noncomputable section

/-! ### Trivializing covers of a free isometric action -/

section Cover

variable {H : Type} [Group H] [Fintype H] {X : Type} [MetricSpace X] [MulAction H X]
  [IsIsometricSMul H X]

omit [IsIsometricSMul H X] in
/-- At every point of a free isometric action of a finite group the translates are separated. -/
theorem exists_sep_radius (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) (x : X) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : H, h ≠ 1 → 4 * ε < dist (h • x) x := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ h : H, h ≠ 1 → 4 * ε < dist (h • x) x := by
    refine eventually_mem_nhdsWithin.and ?_
    rw [Filter.eventually_all]
    intro h
    by_cases hh : h = 1
    · exact Eventually.of_forall fun _ h' ↦ absurd hh h'
    have hd : 0 < dist (h • x) x := dist_pos.2 fun e ↦ hh (hfree h x e)
    have ht : Tendsto (fun ε : ℝ ↦ 4 * ε) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ ↦ 4 * ε := continuous_const.mul continuous_id
      simpa using hc.tendsto 0
    exact nhdsWithin_le_nhds ((ht.eventually (gt_mem_nhds hd)).mono fun _ h' _ ↦ h')
  exact hev.exists

/-- The closed invariant piece `⋃ₕ h • B̄(x, ε)` around an orbit. -/
def orbitPiece (x : X) (ε : ℝ) : Set X := ⋃ h : H, h • closedBall x ε

theorem isClosedInv_orbitPiece (x : X) (ε : ℝ) : IsClosedInv H (orbitPiece (H := H) x ε) := by
  refine ⟨isClosed_iUnion_of_finite fun h ↦ ?_, fun g ↦ ?_⟩
  · rw [Metric.smul_closedBall]
    exact isClosed_closedBall
  · rw [orbitPiece, Set.smul_set_iUnion]
    simp_rw [smul_smul]
    exact (Equiv.mulLeft g).surjective.iUnion_comp (fun h ↦ h • closedBall x ε)

/-- **Trivializing covers** (l.429–431): a compact metric space with a free isometric action of a
finite group is covered by finitely many (at least one) closed invariant pieces, each inside the
translates of an open set whose translates are pairwise disjoint (the hypotheses of
`lemma_6_2`). -/
theorem exists_trivializingCover [CompactSpace X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) :
    ∃ (s : ℕ) (_ : 0 < s) (T : Fin s → Set X) (W₀ : Fin s → Set X),
      (∀ a, IsClosedInv H (T a)) ∧ ⋃ a, T a = Set.univ ∧ (∀ a, IsOpen (W₀ a)) ∧
      (∀ a, ∀ h : H, h ≠ 1 → Disjoint (h • W₀ a) (W₀ a)) ∧ (∀ a, T a ⊆ ⋃ h : H, h • W₀ a) := by
  choose ε hε hsep using exists_sep_radius hfree
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ ball x (ε x))
    (fun _ ↦ isOpen_ball) fun x _ ↦ Set.mem_iUnion.2 ⟨x, mem_ball_self (hε x)⟩
  let pt : Fin (t.card + 1) → Option X := fun a ↦
    if h : (a : ℕ) < t.card then some (t.equivFin.symm ⟨a, h⟩ : X) else none
  let T : Fin (t.card + 1) → Set X := fun a ↦ (pt a).elim ∅ fun x ↦ orbitPiece (H := H) x (ε x)
  let W₀ : Fin (t.card + 1) → Set X := fun a ↦ (pt a).elim ∅ fun x ↦ ball x (2 * ε x)
  refine ⟨t.card + 1, Nat.succ_pos _, T, W₀, fun a ↦ ?_, ?_, fun a ↦ ?_, fun a h hh ↦ ?_,
    fun a ↦ ?_⟩
  · rcases hpa : pt a with _ | x <;> simp only [T, hpa, Option.elim_none, Option.elim_some]
    · exact ⟨isClosed_empty, fun _ ↦ Set.smul_set_empty⟩
    · exact isClosedInv_orbitPiece x (ε x)
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    obtain ⟨k, hk⟩ : ∃ k : Fin t.card, (t.equivFin.symm k : X) = x :=
      ⟨t.equivFin ⟨x, hx⟩, by simp⟩
    refine Set.mem_iUnion.2 ⟨⟨k, k.2.trans (Nat.lt_succ_self _)⟩, ?_⟩
    have hpt : pt ⟨k, k.2.trans (Nat.lt_succ_self _)⟩ = some x := by
      simp only [pt, dif_pos k.2]
      exact congrArg some hk
    simp only [T, hpt, Option.elim_some]
    exact Set.mem_iUnion.2 ⟨1, by rw [one_smul]; exact ball_subset_closedBall hy⟩
  · rcases hpa : pt a with _ | x <;> simp only [W₀, hpa, Option.elim_none, Option.elim_some]
    · exact isOpen_empty
    · exact isOpen_ball
  · rcases hpa : pt a with _ | x <;> simp only [W₀, hpa, Option.elim_none, Option.elim_some]
    · simp
    · rw [Metric.smul_ball]
      exact ball_disjoint_ball (by linarith [hsep x h hh])
  · rcases hpa : pt a with _ | x <;> simp only [T, W₀, hpa, Option.elim_none, Option.elim_some]
    · exact Set.empty_subset _
    · refine Set.iUnion_mono fun h ↦ Set.smul_set_mono ?_
      exact closedBall_subset_ball (by linarith [hε x])

end Cover

/-! ### Theorem 6.3 -/

section Theorem63

variable (𝕃 : LowerLTheory) {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
  [∀ i, Fintype (G i)] (π : ∀ i, G i →* H)

/-- `τ ⊗ −` commutes with forgetting control (`pushTail_comp_tensor`). -/
theorem forgetControl_comp_tensor (X : Type) [MulAction H X] [PseudoEMetricSpace X] {Q : Type}
    [Fintype Q] (ρ : H →* Equiv.Perm Q) :
    forgetControl π X ≫ (AsymptoticCategory.tensorInv ρ :
      asymptoticInvCat π PUnit ⟶ asymptoticInvCat π PUnit) =
      tensorHom π X ρ ≫ forgetControl π X :=
  InvCat.hom_ext (pushTail_comp_tensor ρ (fun _ _ ↦ rfl) uniformContinuous_const)

/-- **Theorem 6.3** (l.443–452) for a free isometric action of a group `H` of prime order `p` on a
compact metric space `X`: if `|Gᵢ| = p ^ (kᵢ + 1)` and `πᵢ(gᵢ) ≠ 1`, every class
`α ∈ L_4(𝒜_G(X))` has `σ_tail(α)` (after forgetting control) divisible by `p` at all large
indices.  Lemma 6.2 for a trivializing cover (`exists_trivializingCover`), naturality of
`τ ⊗ −` under forgetting control, and `σtail_liftPred_dvd`. -/
theorem σtail_forgetControl_liftPred_dvd [Fintype H] [∀ i, DecidableEq (G i)] {X : Type}
    [MetricSpace X] [CompactSpace X] [MulAction H X] [IsIsometricSMul H X]
    (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) {p : ℕ} (hp : p.Prime)
    (hH : Fintype.card H = p) (k : ℕ → ℕ) (hG : ∀ i, Fintype.card (G i) = p ^ (k i + 1))
    (g : ∀ i, G i) (hg : ∀ i, π i (g i) ≠ 1) (x : 𝕃.L (asymptoticInvCat π X) 4) :
    (𝕃.σtail π (𝕃.map (forgetControl π X) 4 x)).LiftPred fun z ↦ (p : ℤ) ∣ z := by
  obtain ⟨s, hs, T, W₀, hT, hcover, hW₀, hdisj, hTW⟩ := exists_trivializingCover (H := H) hfree
  have h62 := lemma_6_2 π 𝕃 hs T hT hcover W₀ hW₀ hdisj hTW 4
  letI : ∀ i, MulAction (G i) H := fun i ↦ MulAction.compHom H ((tauAction H).comp (π i))
  refine 𝕃.σtail_liftPred_dvd π H _ (FreeQG.toPoint_tensorInv G π (tauAction H))
    (𝕃.mapEnd (AsymptoticCategory.tensorInv (tauAction H)) 4) (fun _ ↦ rfl) (s := s) hp k hG g
    (fun i q h ↦ hg i (mul_eq_right.mp (show π i (g i) * q = q from h))) _ ?_
  rw [← map_nu_pow_comm (𝕃.map (forgetControl π X) 4) (𝕃.mapEnd (tensorHom π X (tauAction H)) 4)
    _ (fun a ↦ by
      change 𝕃.map _ 4 (𝕃.map _ 4 a) = 𝕃.map _ 4 (𝕃.map _ 4 a)
      rw [LowerLTheory.map_comp_apply, LowerLTheory.map_comp_apply,
        forgetControl_comp_tensor]) p s x, ← hH, h62]
  exact map_zero _

/-- **Theorem 6.3 for the control data of §7** (l.443–452, (12.2)): for the free scalar
`C_p`-sphere `T = S^{2m-1}` of `cd` and tail groups `Gᵢ ↠ C_p`, every `α ∈ L_4(𝒜_G(T))` has
tail signature `σ_tail(α)` (after forgetting control, Prop. 3.2) in `∏ pℤ / ⊕ pℤ`. -/
theorem theorem_6_3 {p : ℕ} [hp : Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    [∀ i, DecidableEq (Γ.G i)]
    (x : 𝕃.L (asymptoticInvCat Γ.π (sphere (0 : EuclideanSpace ℂ (Fin cd.m)) 1)) 4) :
    𝕃.σtail Γ.π (𝕃.map (cd.forgetControlT Γ) 4 x) ∈ divTail p := by
  haveI : Finite cd.Cp := Nat.finite_of_card_ne_zero (by rw [cd.card_Cp]; exact hp.out.ne_zero)
  letI : Fintype cd.Cp := Fintype.ofFinite _
  have hH : Fintype.card cd.Cp = p := by rw [← Nat.card_eq_fintype_card, cd.card_Cp]
  have hcard (i : ℕ) : ∃ k, Fintype.card (Γ.G i) = p ^ (k + 1) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := Γ.G i)).mp (Γ.isPGroup i)
    have hdvd := Subgroup.card_dvd_of_surjective (Γ.surjective i)
    rw [cd.card_Cp, hn] at hdvd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_add_one.mpr <| Nat.pos_of_ne_zero fun h0 ↦
      hp.out.one_lt.ne' (Nat.dvd_one.mp (by simpa [h0] using hdvd))
    exact ⟨k, by rw [← Nat.card_eq_fintype_card, hn]⟩
  choose k hk using hcard
  have hgen (i : ℕ) : ∃ g : Γ.G i, Γ.π i g ≠ 1 := by
    haveI : Nontrivial cd.Cp :=
      Fintype.one_lt_card_iff_nontrivial.mp (by rw [hH]; exact hp.out.one_lt)
    obtain ⟨c, hc⟩ := exists_ne (1 : cd.Cp)
    obtain ⟨g, rfl⟩ := Γ.surjective i c
    exact ⟨g, hc⟩
  choose g hg using hgen
  exact σtail_forgetControl_liftPred_dvd 𝕃 Γ.π (fun h v hv ↦ Subtype.ext
    (eq_one_of_smul_sphere_eq (z := (h : Circle)) hv)) hp.out hH k hk g hg x

end Theorem63

/-! ### Naturality of Mayer–Vietoris boundaries (abstract) -/

namespace LowerLTheory

variable (𝕃 : LowerLTheory)

/-- **Naturality of the Mayer–Vietoris boundary** `mvBdryOf` (l.239) for maps of filtrations
`α : F → F₂`, `β : F' → F₂'` compatible with the excisions and with the identifications of the
subcategories. -/
theorem mvBdryOf_natural {A B A₂ B₂ : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
    {F₂ : KaroubiFiltration A₂} {F₂' : KaroubiFiltration B₂} {Φ : FiltrationHom F F'}
    {Φ₂ : FiltrationHom F₂ F₂'} (hΦ : IsUnitaryEquiv Φ.quot) (hΦ₂ : IsUnitaryEquiv Φ₂.quot)
    {C₁ C₂ : InvCat} (u₁ : F.sub ≅ C₁) (u₂ : F₂.sub ≅ C₂) (α : FiltrationHom F F₂)
    (β : FiltrationHom F' F₂') (c : C₁ ⟶ C₂) (hαβ : Φ.toHom ≫ β.toHom = α.toHom ≫ Φ₂.toHom)
    (hc : u₁.hom ≫ c = α.sub ≫ u₂.hom) (n : ℤ) :
    (𝕃.map c n).comp (𝕃.mvBdryOf Φ hΦ u₁ n) =
      (𝕃.mvBdryOf Φ₂ hΦ₂ u₂ n).comp (𝕃.map β.toHom (n + 1)) := by
  ext x
  have h := DFunLike.congr_fun
    (𝕃.cutOf_natural hΦ hΦ₂ F'.proj F₂'.proj α β β.toHom hαβ β.comp_proj.symm n) x
  simp only [AddMonoidHom.comp_apply] at h
  change 𝕃.map c n (𝕃.map u₁.hom n (𝕃.cutOf hΦ F'.proj n x)) =
    𝕃.map u₂.hom n (𝕃.cutOf hΦ₂ F₂'.proj n (𝕃.map β.toHom (n + 1) x))
  rw [← h, map_comp_apply, map_comp_apply, hc]

end LowerLTheory

/-! ### Support-compatible functors and the naturality of the cuts -/

section MV41

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {X : Type} [MulAction H X] [PseudoEMetricSpace X] [CompactSpace X] [IsIsometricSMul H X]

variable (π : ∀ i, G i →* H) in
/-- The Mayer–Vietoris boundary `L_{n+1}(𝒜_{A∪B}) → L_n(𝒜_{A∩B})` of closed invariant `A, B`
(the boundary of `mvSystem`, indexed by sets rather than lattice elements). -/
def mvBdry41 (𝕃 : LowerLTheory) {A B : Set X} (hA : IsClosedInv H A) (hB : IsClosedInv H B)
    (n : ℤ) :
    𝕃.L (supportKaroubiFiltration π (A ∪ B)).sub (n + 1) →+
      𝕃.L (supportKaroubiFiltration π (A ∩ B)).sub n :=
  𝕃.mvBdryOf (excisionHom π A B) (isUnitaryEquiv_excision hA hB)
    (supportRestrictSubIso (π := π) (Set.inter_subset_left : A ∩ B ⊆ A)) n

end MV41

section Abstract

/-! Identities between functors of full subcategories, proved for abstract filtrations (for the
concrete support conditions the kernel would unfold them expensively). -/

variable {A B : InvCat} (Θ : A ⟶ B)

theorem subMap_comp_filtSub {F₁ F₂ : KaroubiFiltration A} {F₁' F₂' : KaroubiFiltration B}
    (h : ∀ X, F₁.U X → F₂.U X) (h' : ∀ X, F₁'.U X → F₂'.U X)
    (h₁ : ∀ X, F₁.U X → F₁'.U (Θ.F.obj X)) (h₂ : ∀ X, F₂.U X → F₂'.U (Θ.F.obj X)) :
    A.subMap h ≫ (⟨Θ, h₂⟩ : FiltrationHom F₂ F₂').sub =
      (⟨Θ, h₁⟩ : FiltrationHom F₁ F₁').sub ≫ B.subMap h' :=
  rfl

theorem restrictSubIso_comp_filtSub {F G : KaroubiFiltration A} {F' G' : KaroubiFiltration B}
    [G.U.IsStableUnderRetracts] [G'.U.IsStableUnderRetracts]
    (hFG : ∀ X, F.U X → G.U X) (hF'G' : ∀ X, F'.U X → G'.U X)
    (hF : ∀ X, F.U X → F'.U (Θ.F.obj X)) (hG : ∀ X, G.U X → G'.U (Θ.F.obj X))
    (hR : ∀ X, (F.restrict G.U).U X →
      (F'.restrict G'.U).U ((⟨Θ, hG⟩ : FiltrationHom G G').sub.F.obj X)) :
    (F.restrictSubIso G.U hFG).hom ≫ (⟨Θ, hF⟩ : FiltrationHom F F').sub =
      (⟨(⟨Θ, hG⟩ : FiltrationHom G G').sub, hR⟩ :
        FiltrationHom (F.restrict G.U) (F'.restrict G'.U)).sub ≫
        (F'.restrictSubIso G'.U hF'G').hom :=
  rfl

end Abstract

section SupportHom

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]
  {H' : Type} [Group H'] {G' : ℕ → Type} [∀ i, Group (G' i)] [∀ i, Fintype (G' i)]
  {π' : ∀ i, G' i →* H'} {X' : Type} [MulAction H' X'] [PseudoEMetricSpace X']

variable (π π') in
/-- A morphism `𝒜_G(X) ⟶ 𝒜_{G'}(X')` carrying `𝒜_S(X)` into `𝒜_{S'}(X')` whenever `j(S) ⊆ S'`
(e.g. forgetting the group and pushing forward along `j`). -/
structure SupportHom (j : X → X') where
  toHom : asymptoticInvCat π X ⟶ asymptoticInvCat π' X'
  map_mem : ∀ {S : Set X} {S' : Set X'}, Set.MapsTo j S S' → ∀ P,
    (supportKaroubiFiltration π S).U P → (supportKaroubiFiltration π' S').U (toHom.F.obj P)

namespace SupportHom

variable {j : X → X'} (Φ : SupportHom π π' j)

/-- `Φ` as a map of support filtrations `(𝒜_S ⊂ 𝒜) → (𝒜_{S'} ⊂ 𝒜')`. -/
def filt {S : Set X} {S' : Set X'} (h : Set.MapsTo j S S') :
    FiltrationHom (supportKaroubiFiltration π S) (supportKaroubiFiltration π' S') :=
  ⟨Φ.toHom, Φ.map_mem h⟩

/-- `Φ` restricted to `𝒜_S → 𝒜_{S'}`. -/
abbrev sub {S : Set X} {S' : Set X'} (h : Set.MapsTo j S S') :
    (supportKaroubiFiltration π S).sub ⟶ (supportKaroubiFiltration π' S').sub :=
  (Φ.filt h).sub

/-- `Φ` as a map of the filtrations `(𝒜_Y ⊂ 𝒜_A) → (𝒜_{Y'} ⊂ 𝒜_{A'})`. -/
def restrictFilt {Y A : Set X} {Y' A' : Set X'} (hY : Set.MapsTo j Y Y')
    (hA : Set.MapsTo j A A') :
    FiltrationHom (supportRestrictFiltration π Y A) (supportRestrictFiltration π' Y' A') :=
  ⟨Φ.sub hA, fun P h ↦ Φ.map_mem hY P.obj h⟩

theorem supportIncl_comp_sub {S T : Set X} {S' T' : Set X'} (hST : S ⊆ T) (hST' : S' ⊆ T')
    (hS : Set.MapsTo j S S') (hT : Set.MapsTo j T T') :
    supportIncl (π := π) hST ≫ Φ.sub hT = Φ.sub hS ≫ supportIncl hST' :=
  subMap_comp_filtSub Φ.toHom _ _ _ _

theorem map_supportIncl (𝕃 : LowerLTheory) {S T : Set X} {S' T' : Set X'} (hST : S ⊆ T)
    (hST' : S' ⊆ T') (hS : Set.MapsTo j S S') (hT : Set.MapsTo j T T') (n : ℤ) :
    (𝕃.map (Φ.sub hT) n).comp (𝕃.map (supportIncl (π := π) hST) n) =
      (𝕃.map (supportIncl hST') n).comp (𝕃.map (Φ.sub hS) n) :=
  𝕃.map_comp_eq (Φ.supportIncl_comp_sub hST hST' hS hT) n

variable [CompactSpace X] [IsIsometricSMul H X] [CompactSpace X'] [IsIsometricSMul H' X']

/-- **Naturality of the Mayer–Vietoris boundary** `mvBdry41` (l.239). -/
theorem mvBdry41_natural (𝕃 : LowerLTheory) {A B : Set X} {A' B' : Set X'} (hA : IsClosedInv H A)
    (hB : IsClosedInv H B) (hA' : IsClosedInv H' A') (hB' : IsClosedInv H' B')
    (mA : Set.MapsTo j A A') (mB : Set.MapsTo j B B') (n : ℤ) :
    (𝕃.map (Φ.sub (mA.inter_inter mB)) n).comp (mvBdry41 π 𝕃 hA hB n) =
      (mvBdry41 π' 𝕃 hA' hB' n).comp (𝕃.map (Φ.sub (mA.union_union mB)) (n + 1)) :=
  𝕃.mvBdryOf_natural _ _ _ _ (Φ.restrictFilt (mA.inter_inter mB) mA)
    (Φ.restrictFilt mB (mA.union_union mB)) _
    (subMap_comp_filtSub Φ.toHom (fun _ h ↦ IsSupported.mono Set.subset_union_left h)
      (fun _ h ↦ IsSupported.mono Set.subset_union_left h) _ _)
    (restrictSubIso_comp_filtSub Φ.toHom _ _ _ _ _) n

/-- **Naturality of the separated projection** `projSep`. -/
theorem projSep_natural (𝕃 : LowerLTheory) {Y Z S : Set X} {Y' Z' S' : Set X'}
    (hY : IsClosedInv H Y) (hZ : IsClosedInv H Z) (hYS : Y ⊆ S) (hZS : Z ⊆ S) (hS : S ⊆ Y ∪ Z)
    (hYZ : Disjoint Y Z) (hY' : IsClosedInv H' Y') (hZ' : IsClosedInv H' Z') (hYS' : Y' ⊆ S')
    (hZS' : Z' ⊆ S') (hS' : S' ⊆ Y' ∪ Z') (hYZ' : Disjoint Y' Z') (mY : Set.MapsTo j Y Y')
    (mZ : Set.MapsTo j Z Z') (mS : Set.MapsTo j S S') (n : ℤ) :
    (𝕃.map (Φ.sub mY) n).comp (projSep 𝕃 hY hZ hYS hZS hS hYZ n) =
      (projSep 𝕃 hY' hZ' hYS' hZS' hS' hYZ' n).comp (𝕃.map (Φ.sub mS) n) := by
  ext x
  have hsq := subMap_comp_filtSub Φ.toHom (F₁ := supportKaroubiFiltration π Y)
    (F₂ := supportKaroubiFiltration π S) (F₁' := supportKaroubiFiltration π' Y')
    (F₂' := supportKaroubiFiltration π' S') (fun _ h ↦ IsSupported.mono hYS h)
    (fun _ h ↦ IsSupported.mono hYS' h) (Φ.map_mem mY) (Φ.map_mem mS)
  have h : (supportIncl (π := π) hYS ≫ (supportRestrictFiltration π Z S).proj) ≫
      (Φ.restrictFilt mZ mS).quot =
      Φ.sub mY ≫ (supportIncl (π := π') hYS' ≫ (supportRestrictFiltration π' Z' S').proj) := by
    rw [assoc, ← FiltrationHom.comp_proj, ← assoc, ← assoc]
    exact congrArg (· ≫ (supportRestrictFiltration π' Z' S').proj) hsq
  simp only [projSep, LowerLTheory.projSepOf, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine (𝕃.equivOf_symm_natural (isUnitaryEquiv_sep hY hZ hYS hZS hS hYZ)
    (isUnitaryEquiv_sep hY' hZ' hYS' hZS' hS' hYZ') _ _ h n _).symm.trans (congrArg _ ?_)
  exact (𝕃.map_comp_apply _ _ n x).trans ((congrArg (fun Θ ↦ 𝕃.map Θ n x)
    (FiltrationHom.comp_proj (Φ.restrictFilt mZ mS)).symm).trans (𝕃.map_comp_apply _ _ n x).symm)

/-- **Naturality of the exterior cut (4.2)** (l.239): the square of (11.2) for one cut. -/
theorem cutBdry_natural (𝕃 : LowerLTheory) {A B Z : Set X} {A' B' Z' : Set X'}
    (hA : IsClosedInv H A) (hB : IsClosedInv H B) (hZ : IsClosedInv H Z)
    (hcover : A ∪ B = Set.univ) (hZA : Z ⊆ A) (hZB : Disjoint Z B)
    (hA' : IsClosedInv H' A') (hB' : IsClosedInv H' B') (hZ' : IsClosedInv H' Z')
    (hcover' : A' ∪ B' = Set.univ) (hZA' : Z' ⊆ A') (hZB' : Disjoint Z' B')
    (mA : Set.MapsTo j A A') (mB : Set.MapsTo j B B') (mZ : Set.MapsTo j Z Z') (n : ℤ) :
    (𝕃.map (Φ.sub (mA.inter_inter mB)) n).comp (cutBdry 𝕃 hA hB hZ hcover hZA hZB n) =
      (cutBdry 𝕃 hA' hB' hZ' hcover' hZA' hZB' n).comp (𝕃.map (Φ.filt mZ).quot (n + 1)) := by
  have mBZ := mB.union_union mZ
  have mS := mA.inter_inter mBZ
  have hsep := Φ.projSep_natural 𝕃 (hA.inter hB) hZ
    (Set.inter_subset_inter_right A Set.subset_union_left)
    (Set.subset_inter hZA Set.subset_union_right)
    (fun _ ⟨hxA, hx⟩ ↦ hx.elim (fun hxB ↦ Or.inl ⟨hxA, hxB⟩) Or.inr)
    (hZB.symm.mono_left Set.inter_subset_right) (hA'.inter hB') hZ'
    (Set.inter_subset_inter_right A' Set.subset_union_left)
    (Set.subset_inter hZA' Set.subset_union_right)
    (fun _ ⟨hxA, hx⟩ ↦ hx.elim (fun hxB ↦ Or.inl ⟨hxA, hxB⟩) Or.inr)
    (hZB'.symm.mono_left Set.inter_subset_right) (mA.inter_inter mB) mZ mS n
  have hiso : (𝕃.map (Φ.sub mS) n).comp
      (𝕃.map (supportRestrictSubIso (π := π) (Set.inter_subset_left : A ∩ (B ∪ Z) ⊆ A)).hom n) =
      (𝕃.map (supportRestrictSubIso (π := π') (Set.inter_subset_left : A' ∩ (B' ∪ Z') ⊆ A')).hom
        n).comp (𝕃.map (Φ.restrictFilt mS mA).sub n) :=
    𝕃.map_comp_eq (restrictSubIso_comp_filtSub Φ.toHom
    (F := supportKaroubiFiltration π (A ∩ (B ∪ Z))) (G := supportKaroubiFiltration π A)
    (F' := supportKaroubiFiltration π' (A' ∩ (B' ∪ Z'))) (G' := supportKaroubiFiltration π' A')
    (fun _ h ↦ IsSupported.mono Set.inter_subset_left h)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_left h) (Φ.map_mem mS) (Φ.map_mem mA)
    (fun P h ↦ Φ.map_mem mS P.obj h)) n
  have hq : (supportFiltrationHom (π := π) (Set.subset_union_right : Z ⊆ B ∪ Z)).quot ≫
      (Φ.filt mBZ).quot = (Φ.filt mZ).quot ≫
        (supportFiltrationHom (π := π') (Set.subset_union_right : Z' ⊆ B' ∪ Z')).quot := by
    rw [← FiltrationHom.comp_quot, ← FiltrationHom.comp_quot]
    congr 1
  have hcut := 𝕃.cutOf_natural
    (isUnitaryEquiv_exteriorExcision hA (hB.union hZ)
      (by rw [← Set.union_assoc, hcover, Set.univ_union]))
    (isUnitaryEquiv_exteriorExcision hA' (hB'.union hZ')
      (by rw [← Set.union_assoc, hcover', Set.univ_union]))
    _ _ (Φ.restrictFilt mS mA) (Φ.filt mBZ) _ (Φ.filt mA).incl_comp hq n
  ext x
  have e1 := DFunLike.congr_fun hsep
  have e2 := DFunLike.congr_fun hiso
  have e3 := DFunLike.congr_fun hcut x
  simp only [AddMonoidHom.comp_apply] at e1 e2 e3 ⊢
  simp only [cutBdry, AddMonoidHom.comp_apply]
  rw [e1, e2, e3]

end SupportHom

end SupportHom

/-! ### Cut flags and the iterated boundary `Δ` of (11.1) -/

section CutFlag

variable (H : Type) [Group H] (X : Type) [MulAction H X] [PseudoEMetricSpace X]

/-- **The cut data of (11.1)** on `X` for the exterior `Z`, with `m` Mayer–Vietoris cuts after
the exterior cut: the cover `X = A ∪ B` of (4.2) with `Z ⊆ A`, `Z ∩ B = ∅` (in §11,
`A = T × (Sⁿ ∖ B(y, r))`, `B = T × B̄(y, r)`); supports `Y k` with `A ∩ B ⊆ Y m`; the cuts
`Y (k + 1) ⊆ a k ∪ b k` with `a k ∩ b k ⊆ Y k` (closed hemispheres of the interfaces
`T × S^{k+1}`); and the split `Y 0 = P ⊔ Q` of `T × S⁰`, `P` the positive component. -/
structure CutFlag (Z : Set X) (m : ℕ) where
  A : Set X
  B : Set X
  Y : ℕ → Set X
  a : ℕ → Set X
  b : ℕ → Set X
  P : Set X
  Q : Set X
  hZ : IsClosedInv H Z
  hA : IsClosedInv H A
  hB : IsClosedInv H B
  ha : ∀ k, IsClosedInv H (a k)
  hb : ∀ k, IsClosedInv H (b k)
  hP : IsClosedInv H P
  hQ : IsClosedInv H Q
  cover : A ∪ B = Set.univ
  ZA : Z ⊆ A
  ZB : Disjoint Z B
  top : A ∩ B ⊆ Y m
  succ : ∀ k, Y (k + 1) ⊆ a k ∪ b k
  inter : ∀ k, a k ∩ b k ⊆ Y k
  PY : P ⊆ Y 0
  QY : Q ⊆ Y 0
  YPQ : Y 0 ⊆ P ∪ Q
  PQ : Disjoint P Q

variable {H X}

namespace CutFlag

variable {H' : Type} [Group H'] {X' : Type} [MulAction H' X'] [PseudoEMetricSpace X']
  {Z : Set X} {Z' : Set X'} {m : ℕ}

/-- `j` maps every set of the flag `F` into the corresponding set of `F'`. -/
structure MapsTo (j : X → X') (F : CutFlag H X Z m) (F' : CutFlag H' X' Z' m) : Prop where
  Z : Set.MapsTo j Z Z'
  A : Set.MapsTo j F.A F'.A
  B : Set.MapsTo j F.B F'.B
  Y : ∀ k, Set.MapsTo j (F.Y k) (F'.Y k)
  a : ∀ k, Set.MapsTo j (F.a k) (F'.a k)
  b : ∀ k, Set.MapsTo j (F.b k) (F'.b k)
  P : Set.MapsTo j F.P F'.P
  Q : Set.MapsTo j F.Q F'.Q

variable [CompactSpace X] [IsIsometricSMul H X] {G : ℕ → Type} [∀ i, Group (G i)]
  [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) (𝕃 : LowerLTheory) (F : CutFlag H X Z m)

/-- The support categories `C k = 𝒜_{Y k}(X)` of the flag. -/
abbrev C (k : ℕ) : InvCat := (supportKaroubiFiltration π (F.Y k)).sub

/-- The exterior cut (4.2), `L_{n+1}(ℬ_Z(X)) → L_n(𝒜_{Y m}(X))`. -/
def cut (n : ℤ) : 𝕃.L (exteriorInvCat π Z) (n + 1) →+ 𝕃.L (F.C π m) n :=
  (𝕃.map (supportIncl F.top) n).comp (cutBdry 𝕃 F.hA F.hB F.hZ F.cover F.ZA F.ZB n)

/-- The `k`-th hemisphere cut (4.1), `L_{n+1}(𝒜_{Y (k+1)}) → L_n(𝒜_{Y k})`. -/
def mvCut (k : ℕ) (n : ℤ) : 𝕃.L (F.C π (k + 1)) (n + 1) →+ 𝕃.L (F.C π k) n :=
  (𝕃.map (supportIncl (F.inter k)) n).comp
    ((mvBdry41 π 𝕃 (F.ha k) (F.hb k) n).comp
      (𝕃.map (supportIncl (F.succ k)) (n + 1)))

/-- **The iterated boundary (11.1)** `L_{m+d+1}(ℬ_Z(X)) → L_d(𝒜_P(X))`: the exterior cut, the
`m` hemisphere cuts (`iterDown`) and the projection to the positive component `P` of `Y 0`. -/
def delta (d : ℤ) : 𝕃.L (exteriorInvCat π Z) ((m : ℤ) + d + 1) →+
    𝕃.L (supportKaroubiFiltration π F.P).sub d :=
  (projSep 𝕃 F.hP F.hQ F.PY F.QY F.YPQ F.PQ d).comp
    ((𝕃.iterDown (F.C π) d (fun k ↦ F.mvCut π 𝕃 k ((k : ℤ) + d)) m).comp
      (F.cut π 𝕃 ((m : ℤ) + d)))

variable [CompactSpace X'] [IsIsometricSMul H' X'] {G' : ℕ → Type} [∀ i, Group (G' i)]
  [∀ i, Fintype (G' i)] {π' : ∀ i, G' i →* H'} {j : X → X'} (Φ : SupportHom π π' j)
  {F' : CutFlag H' X' Z' m}

theorem cut_natural (hF : MapsTo j F F') (n : ℤ) :
    (𝕃.map (Φ.sub (hF.Y m)) n).comp (F.cut π 𝕃 n) =
      (F'.cut π' 𝕃 n).comp (𝕃.map (Φ.filt hF.Z).quot (n + 1)) := by
  ext x
  have e1 := DFunLike.congr_fun (Φ.map_supportIncl 𝕃 F.top F'.top (hF.A.inter_inter hF.B)
    (hF.Y m) n)
  have e2 := DFunLike.congr_fun (Φ.cutBdry_natural 𝕃 F.hA F.hB F.hZ F.cover F.ZA F.ZB F'.hA
    F'.hB F'.hZ F'.cover F'.ZA F'.ZB hF.A hF.B hF.Z n) x
  simp only [AddMonoidHom.comp_apply] at e1 e2 ⊢
  simp only [cut, AddMonoidHom.comp_apply]
  rw [e1, e2]

omit [CompactSpace X'] [IsIsometricSMul H' X'] in
theorem mvCut_apply (k : ℕ) (n : ℤ) (x : 𝕃.L (F.C π (k + 1)) (n + 1)) :
    F.mvCut π 𝕃 k n x = 𝕃.map (supportIncl (F.inter k)) n
      (mvBdry41 π 𝕃 (F.ha k) (F.hb k) n (𝕃.map (supportIncl (F.succ k)) (n + 1) x)) := by
  simp only [mvCut, AddMonoidHom.comp_apply]

omit [CompactSpace X'] [IsIsometricSMul H' X'] in
theorem delta_apply (d : ℤ) (x : 𝕃.L (exteriorInvCat π Z) ((m : ℤ) + d + 1)) :
    F.delta π 𝕃 d x = projSep 𝕃 F.hP F.hQ F.PY F.QY F.YPQ F.PQ d
      (𝕃.iterDown (F.C π) d (fun k ↦ F.mvCut π 𝕃 k ((k : ℤ) + d)) m
        (F.cut π 𝕃 ((m : ℤ) + d) x)) :=
  rfl

private theorem mvCut_natural_aux₁ (hF : MapsTo j F F') (k : ℕ) (n : ℤ)
    (x : 𝕃.L (supportKaroubiFiltration π (F.a k ∪ F.b k)).sub (n + 1)) :
    𝕃.map (supportIncl (F'.inter k)) n (𝕃.map (Φ.sub ((hF.a k).inter_inter (hF.b k))) n
      (mvBdry41 π 𝕃 (F.ha k) (F.hb k) n x)) =
    𝕃.map (supportIncl (F'.inter k)) n (mvBdry41 π' 𝕃 (F'.ha k) (F'.hb k) n
      (𝕃.map (Φ.sub ((hF.a k).union_union (hF.b k))) (n + 1) x)) := by
  have e := DFunLike.congr_fun (Φ.mvBdry41_natural 𝕃 (F.ha k) (F.hb k) (F'.ha k) (F'.hb k)
    (hF.a k) (hF.b k) n) x
  simp only [AddMonoidHom.comp_apply] at e
  rw [e]

omit [CompactSpace X] [IsIsometricSMul H X] [CompactSpace X'] [IsIsometricSMul H' X'] in
private theorem mvCut_natural_aux₂ (hF : MapsTo j F F') (k : ℕ) (n : ℤ)
    (x : 𝕃.L (F.C π (k + 1)) (n + 1)) :
    𝕃.map (Φ.sub ((hF.a k).union_union (hF.b k))) (n + 1)
      (𝕃.map (supportIncl (F.succ k)) (n + 1) x) =
    𝕃.map (supportIncl (F'.succ k)) (n + 1) (𝕃.map (Φ.sub (hF.Y (k + 1))) (n + 1) x) := by
  have e := DFunLike.congr_fun (Φ.map_supportIncl 𝕃 (F.succ k) (F'.succ k) (hF.Y (k + 1))
    ((hF.a k).union_union (hF.b k)) (n + 1)) x
  simpa using e

theorem mvCut_natural (hF : MapsTo j F F') (k : ℕ) (n : ℤ) :
    (𝕃.map (Φ.sub (hF.Y k)) n).comp (F.mvCut π 𝕃 k n) =
      (F'.mvCut π' 𝕃 k n).comp (𝕃.map (Φ.sub (hF.Y (k + 1))) (n + 1)) := by
  ext x
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, mvCut_apply π 𝕃 F, mvCut_apply π' 𝕃 F']
  have e1 := DFunLike.congr_fun (Φ.map_supportIncl 𝕃 (F.inter k) (F'.inter k)
    ((hF.a k).inter_inter (hF.b k)) (hF.Y k) n)
  simp only [AddMonoidHom.comp_apply] at e1
  rw [e1, mvCut_natural_aux₁ π 𝕃 F Φ hF, mvCut_natural_aux₂ π 𝕃 F Φ hF]

/-- **(11.2)**: the iterated boundaries of flags related by `j` commute with a support-compatible
functor along `j` (`cutBdry_natural`, `mvBdry41_natural`, `projSep_natural`,
`iterDown_natural`). -/
theorem delta_natural (hF : MapsTo j F F') (d : ℤ) :
    (𝕃.map (Φ.sub hF.P) d).comp (F.delta π 𝕃 d) =
      (F'.delta π' 𝕃 d).comp (𝕃.map (Φ.filt hF.Z).quot ((m : ℤ) + d + 1)) := by
  have hiter := 𝕃.iterDown_natural (fun k ↦ Φ.sub (hF.Y k)) d
    (fun k ↦ F.mvCut_natural π 𝕃 Φ hF k ((k : ℤ) + d)) m
  have hsep := Φ.projSep_natural 𝕃 F.hP F.hQ F.PY F.QY F.YPQ F.PQ F'.hP F'.hQ F'.PY F'.QY F'.YPQ
    F'.PQ hF.P hF.Q (hF.Y 0) d
  ext x
  have e1 := DFunLike.congr_fun hsep
  have e2 := DFunLike.congr_fun hiter
  have e3 := DFunLike.congr_fun (F.cut_natural π 𝕃 Φ hF ((m : ℤ) + d)) x
  simp only [AddMonoidHom.comp_apply] at e1 e2 e3
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, delta_apply, delta_apply, e1, e2, e3]

end CutFlag

end CutFlag

end

end HSFormal.LTheory

/-! ### The round sphere: ambient coordinates -/

namespace HSFormal.RoundSphere

open Metric
open scoped Pointwise

noncomputable section

variable {n : ℕ}

/-- The ambient coordinates `Sⁿ ⊂ ℝⁿ⁺¹` of a point of the round sphere (`roundSphere`). -/
def amb (z : RoundSphere n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (roundSphere n (toOnePoint z) : EuclideanSpace ℝ (Fin (n + 1)))

theorem continuous_amb : Continuous (amb (n := n)) :=
  continuous_subtype_val.comp ((roundSphere n).continuous.comp toOnePoint.continuous)

theorem norm_amb (z : RoundSphere n) : ‖amb z‖ = 1 :=
  norm_eq_of_mem_sphere (roundSphere n (toOnePoint z))

theorem dist_eq_norm_amb (z z' : RoundSphere n) : dist z z' = ‖amb z - amb z'‖ := by
  rw [dist_eq, roundDist, Subtype.dist_eq, dist_eq_norm]
  rfl

theorem amb_infty : amb (infty : RoundSphere n) = northPole n := by
  simp only [amb, infty, Homeomorph.apply_symm_apply]
  exact roundSphere_infty n

/-- A point at round distance `2` from `∞` is the south pole `-e₀`. -/
theorem amb_eq_neg_northPole {y : RoundSphere n} (hy : dist y infty = 2) :
    amb y = -northPole n := by
  have h₁ := norm_add_sq_real (amb y) (northPole n)
  have h₂ := norm_sub_sq_real (amb y) (northPole n)
  rw [← amb_infty, ← dist_eq_norm_amb, hy, amb_infty, norm_amb, norm_northPole] at h₂
  rw [norm_amb, norm_northPole] at h₁
  have h : ‖amb y + northPole n‖ ^ 2 = 0 := by linarith
  rw [eq_neg_iff_add_eq_zero, ← norm_eq_zero]
  exact pow_eq_zero_iff two_ne_zero |>.mp h

/-- The `k`-th ambient coordinate (`0` for `k > n`). -/
def coord (k : ℕ) (z : RoundSphere n) : ℝ :=
  if h : k < n + 1 then amb z ⟨k, h⟩ else 0

theorem continuous_coord (k : ℕ) : Continuous (coord (n := n) k) := by
  by_cases h : k < n + 1
  · have e : coord (n := n) k = fun z ↦ amb z ⟨k, h⟩ := funext fun _ ↦ dif_pos h
    rw [e]
    exact (PiLp.continuous_apply 2 _ _).comp continuous_amb
  · have e : coord (n := n) k = fun _ ↦ 0 := funext fun _ ↦ dif_neg h
    rw [e]
    exact continuous_const

theorem coord_val (z : RoundSphere n) (i : Fin (n + 1)) : coord i z = amb z i := by
  simp [coord, i.2]

/-- The trivial action fixes every subset. -/
theorem smul_set_eq {G : Type*} [Monoid G] (g : G) (S : Set (RoundSphere n)) : g • S = S :=
  Set.image_id S

/-- On the sphere `S_r(y)` about the south pole `y`, with the coordinates `1, …, n-1` zero, the
last coordinate is nonzero (the two points of `S⁰`). -/
theorem coord_last_ne_zero (hn : 0 < n) {y : RoundSphere n} (hy : dist y infty = 2) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2) {z : RoundSphere n} (hz : dist y z = r)
    (h0 : ∀ i, 0 < i → i < n → coord i z = 0) : coord n z ≠ 0 := by
  intro hlast
  have hw := norm_amb z
  rw [dist_eq_norm_amb, amb_eq_neg_northPole hy] at hz
  have hz' : ‖amb z + northPole n‖ = r := by
    rw [← hz, ← norm_neg]
    congr 1
    abel
  have h₁ := norm_add_sq_real (amb z) (northPole n)
  rw [hz', hw, norm_northPole, northPole, EuclideanSpace.inner_single_right] at h₁
  simp only [one_mul, conj_trivial] at h₁
  have h₂ := EuclideanSpace.norm_sq_eq (amb z)
  rw [hw, Finset.sum_eq_add (0 : Fin (n + 1)) (Fin.last n) (by
      rw [Ne, Fin.ext_iff]; simp; omega) (fun c _ hc ↦ ?_) (by simp) (by simp)] at h₂
  · have hl : amb z (Fin.last n) = 0 := by rw [← coord_val]; simpa using hlast
    rw [hl, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h₂
    norm_num at h₂
    have ha1 : amb z 0 < 1 := by nlinarith
    have ha2 : -1 < amb z 0 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr ha1) (neg_lt_iff_pos_add.mp ha2)]
  · have hc0 : 0 < (c : ℕ) := Nat.pos_of_ne_zero fun h ↦ hc.1 (Fin.ext h)
    have hcn : (c : ℕ) < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp c.2) fun h ↦ hc.2 (Fin.ext h)
    rw [← coord_val, h0 c hc0 hcn, norm_zero]
    norm_num

end

end HSFormal.RoundSphere

/-! ### Lifting flags along `T × S → S` and forgetting the group -/

namespace HSFormal.LTheory

open CategoryTheory Category AsymptoticCategory
open scoped Pointwise

noncomputable section

namespace CutFlag

variable {H : Type} [Group H] {n : ℕ} {Z : Set (RoundSphere n)} {m : ℕ}

/-- A flag on the sphere factor, lifted to `T × Sⁿ` (all sets `T × ·`). -/
def lift (T : Type) [MulAction H T] [PseudoEMetricSpace T] (F : CutFlag H (RoundSphere n) Z m) :
    CutFlag H (T × RoundSphere n) (Set.univ ×ˢ Z) m where
  A := Set.univ ×ˢ F.A
  B := Set.univ ×ˢ F.B
  Y k := Set.univ ×ˢ F.Y k
  a k := Set.univ ×ˢ F.a k
  b k := Set.univ ×ˢ F.b k
  P := Set.univ ×ˢ F.P
  Q := Set.univ ×ˢ F.Q
  hZ := ⟨isClosed_univ.prod F.hZ.1, fun h ↦ smul_univ_prod h _⟩
  hA := ⟨isClosed_univ.prod F.hA.1, fun h ↦ smul_univ_prod h _⟩
  hB := ⟨isClosed_univ.prod F.hB.1, fun h ↦ smul_univ_prod h _⟩
  ha k := ⟨isClosed_univ.prod (F.ha k).1, fun h ↦ smul_univ_prod h _⟩
  hb k := ⟨isClosed_univ.prod (F.hb k).1, fun h ↦ smul_univ_prod h _⟩
  hP := ⟨isClosed_univ.prod F.hP.1, fun h ↦ smul_univ_prod h _⟩
  hQ := ⟨isClosed_univ.prod F.hQ.1, fun h ↦ smul_univ_prod h _⟩
  cover := by rw [← Set.prod_union, F.cover, Set.univ_prod_univ]
  ZA := Set.prod_mono subset_rfl F.ZA
  ZB := Set.disjoint_prod.mpr (Or.inr F.ZB)
  top := by rw [Set.prod_inter_prod, Set.inter_self]; exact Set.prod_mono subset_rfl F.top
  succ k := by rw [← Set.prod_union]; exact Set.prod_mono subset_rfl (F.succ k)
  inter k := by
    rw [Set.prod_inter_prod, Set.inter_self]; exact Set.prod_mono subset_rfl (F.inter k)
  PY := Set.prod_mono subset_rfl F.PY
  QY := Set.prod_mono subset_rfl F.QY
  YPQ := by rw [← Set.prod_union]; exact Set.prod_mono subset_rfl F.YPQ
  PQ := Set.disjoint_prod.mpr (Or.inr F.PQ)

/-- The projection `T × Sⁿ → Sⁿ` maps the lifted flag to the flag. -/
theorem mapsTo_lift (T : Type) [MulAction H T] [PseudoEMetricSpace T]
    (F : CutFlag H (RoundSphere n) Z m) : MapsTo Prod.snd (F.lift T) F where
  Z _ h := h.2
  A _ h := h.2
  B _ h := h.2
  Y _ _ h := h.2
  a _ _ h := h.2
  b _ _ h := h.2
  P _ h := h.2
  Q _ h := h.2

end CutFlag

section ForgetPush

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X Y : Type} [MulAction H X] [PseudoEMetricSpace X] [MulAction H Y]
  [PseudoEMetricSpace Y] {j : Y → X} (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)
  (hj : UniformContinuous j)

/-- Forgetting the group and pushing forward along `j`, `𝒜_G(Y) → 𝒜_1(X)`, as a
support-compatible functor. -/
def forgetPush : SupportHom π (scalarHom H) j where
  toHom := (forgetFiltrationHom π (Set.univ : Set Y)).toHom ≫
    (pushFiltrationHom (π := scalarHom H) hjeq hj (Set.mapsTo_univ j Set.univ)).toHom
  map_mem {S _} hS P hP :=
    ((forgetFiltrationHom π S).comp (pushFiltrationHom hjeq hj hS)).map_mem P hP

omit [∀ i, Fintype (G i)] in
/-- Push-forwards compose. -/
theorem pushTailInvCat_comp {W : Type} [MulAction H W] [PseudoEMetricSpace W] [∀ i, Fintype (G i)]
    {j' : X → W} (hjeq' : ∀ (h : H) (x : X), j' (h • x) = h • j' x) (hj' : UniformContinuous j') :
    pushTailInvCat π hjeq hj ≫ pushTailInvCat π hjeq' hj' =
      pushTailInvCat π (j := j' ∘ j) (fun h y ↦ by simp only [Function.comp_apply, hjeq, hjeq'])
        (hj'.comp hj) :=
  InvCat.hom_ext (CategoryTheory.Quotient.lift_unique' _ _ _ rfl)

omit [MulAction H Y] [PseudoEMetricSpace Y] in
/-- `toPoint` is forgetting the group, then forgetting control. -/
theorem toPointInvCat_eq :
    toPointInvCat π X = (AsymptoticCategory.forgetInv :
      asymptoticInvCat π X ⟶ asymptoticInvCat (scalarHom H) X) ≫ forgetControl (scalarHom H) X :=
  rfl

theorem forgetPush_filt_quot {Z : Set Y} {Z' : Set X} (hZ : Set.MapsTo j Z Z') :
    ((forgetPush π hjeq hj).filt hZ).quot =
      (forgetFiltrationHom π Z).quot ≫ (pushFiltrationHom hjeq hj hZ).quot := by
  rw [← FiltrationHom.comp_quot]
  rfl

end ForgetPush

end

end HSFormal.LTheory

/-! ### The cuts fixed by the control data and `Δ_T`, `Δ_1` of (11.1) -/

namespace HSFormal.ControlData

open CategoryTheory Category LTheory AsymptoticCategory RoundSphere Metric

noncomputable section

variable {p : ℕ} (cd : ControlData p)

/-- The free `C_p`-sphere `T = S^{2m-1} ⊆ ℂ^m`. -/
abbrev T : Type := sphere (0 : EuclideanSpace ℂ (Fin cd.m)) 1

/-- The interface `S^k ⊂ S_r(y)` of the `k`-th cut: the sphere `S_r(y)` about the south pole `y`
(an `(n-1)`-sphere in the hyperplane `w₀ = r²/2 - 1`) with the ambient coordinates
`w_{k+1}, …, w_{n-1}` zero. -/
def hemi (k : ℕ) : Set (RoundSphere cd.n) :=
  {z | dist cd.y z = cd.r ∧ ∀ i, k < i → i < cd.n → coord i z = 0}

theorem isClosed_hemi (k : ℕ) : IsClosed (cd.hemi k) := by
  simp only [hemi, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_eq (continuous_const.dist continuous_id) continuous_const).inter
    (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_coord i) continuous_const)

theorem isClosedInv_dist_ge (s : ℝ) : IsClosedInv cd.Cp {z : RoundSphere cd.n | s ≤ dist cd.y z} :=
  ⟨isClosed_le continuous_const (continuous_const.dist continuous_id), fun h ↦ smul_set_eq h _⟩

theorem isClosedInv_of_isClosed {S : Set (RoundSphere cd.n)} (hS : IsClosed S) :
    IsClosedInv cd.Cp S :=
  ⟨hS, fun h ↦ smul_set_eq h _⟩

/-- **The cut flag of §11** (l.885–897) on `Sⁿ`, fixed by `cd`: the first cut
`A = Sⁿ ∖ B(y, r)`, `B = B̄(y, r)` (so `Z₀ ⊆ A`, `Z₀ ∩ B = ∅` as `r < R`), interface `S_r(y)`;
then the closed hemispheres `±w_{k+1} ≥ 0` of the interfaces `S^{k+1}`, with interfaces
`S^k = S^{k+1} ∩ {w_{k+1} = 0}`, down to `S⁰ = {w_n = ±√(1 - (r²/2 - 1)²)}`, and its positive
point `P = {w_n > 0}`.  Here `w = amb` are the ambient coordinates of `Sⁿ ⊂ ℝⁿ⁺¹`, `w₀` the axis
through `∞` and `y = -e₀` (`amb_eq_neg_northPole`). -/
def flag : CutFlag cd.Cp (RoundSphere cd.n) cd.Z₀ (cd.n - 1) where
  A := {z | cd.r ≤ dist cd.y z}
  B := {z | dist cd.y z ≤ cd.r}
  Y := cd.hemi
  a k := cd.hemi (k + 1) ∩ {z | 0 ≤ coord (k + 1) z}
  b k := cd.hemi (k + 1) ∩ {z | coord (k + 1) z ≤ 0}
  P := cd.hemi 0 ∩ {z | 0 ≤ coord cd.n z}
  Q := cd.hemi 0 ∩ {z | coord cd.n z ≤ 0}
  hZ := cd.isClosedInv_dist_ge cd.R
  hA := cd.isClosedInv_dist_ge cd.r
  hB := cd.isClosedInv_of_isClosed
    (isClosed_le (continuous_const.dist continuous_id) continuous_const)
  ha k := cd.isClosedInv_of_isClosed
    ((cd.isClosed_hemi _).inter (isClosed_le continuous_const (continuous_coord _)))
  hb k := cd.isClosedInv_of_isClosed
    ((cd.isClosed_hemi _).inter (isClosed_le (continuous_coord _) continuous_const))
  hP := cd.isClosedInv_of_isClosed
    ((cd.isClosed_hemi _).inter (isClosed_le continuous_const (continuous_coord _)))
  hQ := cd.isClosedInv_of_isClosed
    ((cd.isClosed_hemi _).inter (isClosed_le (continuous_coord _) continuous_const))
  cover := Set.eq_univ_of_forall fun z ↦ le_total cd.r (dist cd.y z)
  ZA _ hz := cd.r_lt_R.le.trans hz
  ZB := Set.disjoint_left.mpr fun _ h₁ h₂ ↦ absurd (le_trans h₁ h₂) (not_le.mpr cd.r_lt_R)
  top _ hz := ⟨le_antisymm hz.2 hz.1, fun i hi hin ↦ absurd hin (by omega)⟩
  succ k z hz := (le_total 0 (coord (k + 1) z)).imp (fun h ↦ ⟨hz, h⟩) fun h ↦ ⟨hz, h⟩
  inter k z hz := ⟨hz.1.1.1, fun i hi hin ↦ by
    by_cases hik : i = k + 1
    · subst hik
      exact le_antisymm hz.2.2 hz.1.2
    · exact hz.1.1.2 i (by omega) hin⟩
  PY := Set.inter_subset_left
  QY := Set.inter_subset_left
  YPQ z hz := (le_total 0 (coord cd.n z)).imp (fun h ↦ ⟨hz, h⟩) fun h ↦ ⟨hz, h⟩
  PQ := Set.disjoint_left.mpr fun _ h₁ h₂ ↦ coord_last_ne_zero cd.n_pos cd.dist_y_infty cd.r_pos
    (cd.r_lt_R.trans cd.R_lt) h₁.1.1 h₁.1.2 (le_antisymm h₂.2 h₁.2)

theorem N_eq : cd.N = ((cd.n - 1 : ℕ) : ℤ) + 4 + 1 := by
  have := cd.n_pos
  simp only [N]
  omega

variable (𝕃 : LowerLTheory) {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* cd.Cp) (F : CutFlag cd.Cp (RoundSphere cd.n) cd.Z₀ (cd.n - 1))

/-- **`Δ_T`** (11.1), `L_N(ℬ_{G,Z}(T × Sⁿ)) → L_4(𝒜_G(T))`, for a cut flag `F` on `Sⁿ` (in
`fibreSignature`, `F = cd.flag`): the `n` cuts of the lifted flag `T × F` (`CutFlag.delta`) and
the identification `𝒜_{T × P}(T × Sⁿ) → 𝒜_G(T)` by projecting to `T`. -/
def deltaT : 𝕃.L (cd.BG π) cd.N →+ 𝕃.L (asymptoticInvCat π cd.T) 4 :=
  (𝕃.map ((supportKaroubiFiltration π (F.lift cd.T).P).incl ≫
    pushTailInvCat π (j := Prod.fst) (fun _ _ ↦ rfl) uniformContinuous_fst) 4).comp
    (((F.lift cd.T).delta π 𝕃 4).comp (𝕃.castDeg _ cd.N_eq).toAddMonoidHom)

/-- **`Δ_1`** (11.1, scalar version), `L_N(ℬ_{1,Z₀}(Sⁿ)) → L_4(𝒜_1(pt))`: the identical cuts `F`
and forgetting control on the point `P`. -/
def delta1 : 𝕃.L cd.B1S cd.N →+ 𝕃.L (asymptoticInvCat (scalarHom cd.Cp) PUnit) 4 :=
  (𝕃.map ((supportKaroubiFiltration (scalarHom cd.Cp) F.P).incl ≫
    forgetControl (scalarHom cd.Cp) (RoundSphere cd.n)) 4).comp
    ((F.delta (scalarHom cd.Cp) 𝕃 4).comp (𝕃.castDeg _ cd.N_eq).toAddMonoidHom)

/-- `U = Res ≫ push` as a support-compatible functor along `T × Sⁿ → Sⁿ`. -/
abbrev forgetPushSnd : SupportHom π (scalarHom cd.Cp) (Prod.snd : cd.X → RoundSphere cd.n) :=
  forgetPush π (j := Prod.snd) (fun _ _ ↦ rfl) uniformContinuous_snd

theorem res_push_eq :
    cd.res π ≫ cd.push =
      ((cd.forgetPushSnd π).filt (fun _ hx ↦ hx.2 : Set.MapsTo Prod.snd cd.Z cd.Z₀)).quot :=
  (forgetPush_filt_quot π _ _ _).symm

/-- On `𝒜_G(T × Sⁿ)`: pushing to `T` and then to the point is forgetting `T × Sⁿ → Sⁿ` and then
pushing to the point. -/
theorem pushFst_toPoint :
    pushTailInvCat π (Y := cd.X) (j := Prod.fst) (fun _ _ ↦ rfl) uniformContinuous_fst ≫
      toPointInvCat π cd.T =
    (cd.forgetPushSnd π).toHom ≫ forgetControl (scalarHom cd.Cp) (RoundSphere cd.n) := by
  have h₁ : pushTailInvCat π (Y := cd.X) (j := Prod.fst) (fun _ _ ↦ rfl) uniformContinuous_fst ≫
      forgetControl π cd.T = forgetControl π cd.X :=
    pushTailInvCat_comp π (j := Prod.fst) _ _ _ _
  have h₂ : pushTailInvCat (scalarHom cd.Cp) (Y := cd.X) (j := Prod.snd) (fun _ _ ↦ rfl)
      uniformContinuous_snd ≫
      forgetControl (scalarHom cd.Cp) (RoundSphere cd.n) = forgetControl (scalarHom cd.Cp) cd.X :=
    pushTailInvCat_comp (scalarHom cd.Cp) (j := Prod.snd) _ _ _ _
  rw [← forgetControl_comp_forgetInv, ← assoc, h₁, forgetControl_comp_forgetInv, toPointInvCat_eq,
    ← h₂]
  rfl

/-- **(11.2)** `U_* Δ_T = Δ_1 U_*` (l.900–912), with `U₄ = toPoint` (forget the group and push to
a point) on the left. -/
theorem toPoint_deltaT :
    (𝕃.map (toPointInvCat π cd.T) 4).comp (cd.deltaT 𝕃 π F) =
      (cd.delta1 𝕃 F).comp (𝕃.map (cd.res π ≫ cd.push) cd.N) := by
  have hF := F.mapsTo_lift cd.T
  have hsq : ((supportKaroubiFiltration π (F.lift cd.T).P).incl ≫
      pushTailInvCat π (j := Prod.fst) (fun _ _ ↦ rfl) uniformContinuous_fst) ≫
        toPointInvCat π cd.T =
      (cd.forgetPushSnd π).sub hF.P ≫ (supportKaroubiFiltration (scalarHom cd.Cp) F.P).incl ≫
        forgetControl (scalarHom cd.Cp) (RoundSphere cd.n) := by
    rw [← assoc, ← FiltrationHom.incl_comp, assoc, assoc, pushFst_toPoint]
    rfl
  have hnat := CutFlag.delta_natural π 𝕃 (F.lift cd.T) (cd.forgetPushSnd π) hF 4
  ext y
  simp only [deltaT, delta1, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  erw [LowerLTheory.map_comp_apply, hsq, ← LowerLTheory.map_comp_apply, res_push_eq,
    ← LowerLTheory.map_castDeg]
  exact congrArg _ (DFunLike.congr_fun hnat _)

end

end HSFormal.ControlData

/-! ### The pinned fibre signature and the transfer step -/

namespace HSFormal

open CategoryTheory LTheory AsymptoticCategory

noncomputable section

/-- A choice of the cut flag of (11.1) for every control data (the cuts must be functions of `cd`
alone, see `FibreSignature`). -/
abbrev FlagChoice : Type :=
  ∀ ⦃p : ℕ⦄ (cd : ControlData p), CutFlag cd.Cp (RoundSphere cd.n) cd.Z₀ (cd.n - 1)

/-- `σ_tail ∘ Δ_1 ∘ 𝕃.cls` for an arbitrary choice of cut flags. -/
def fibreSignatureOf (𝕃 : LowerLTheory) (F : FlagChoice) : FibreSignature := fun _ cd ↦
  (𝕃.σtail (scalarHom cd.Cp)).comp ((cd.delta1 𝕃 (F cd)).comp (𝕃.cls cd.B1S cd.N))

/-- **The fibre tail signature** `σ = σ_tail ∘ Δ_1 ∘ 𝕃.cls` (11.1), (3.5): the decoration map
`Lconc_N → L_N` of `𝕃`, the `n` cuts `Δ_1` fixed by `cd` (`ControlData.flag`: the ball `B(y, r)`
of §11, then closed hemispheres in the ambient coordinates of `Sⁿ ⊂ ℝⁿ⁺¹`, then the positive point
of `S⁰`), and `σ_tail` on `L_4(𝒜_1(pt))`. -/
def fibreSignature (𝕃 : LowerLTheory) : FibreSignature :=
  fibreSignatureOf 𝕃 fun _ cd ↦ cd.flag

/-- **S7–S9, S12b** (`TransferDivisibility`, (12.2)) for every choice of cut flags: by (11.2)
(`toPoint_deltaT`), `toPoint = forgetControl ≫ forget` and `σtail_forget` (S12b),
`σ(U_* x) = σ_tail(forgetControl(Δ_T x))`, which lies in `∏ pℤ / ⊕ pℤ` by Theorem 6.3
(`theorem_6_3`). -/
theorem transferDivisibility_of (𝕃 : LowerLTheory) (F : FlagChoice) :
    TransferDivisibility (fibreSignatureOf 𝕃 F) := by
  intro p _ cd Γ x
  classical
  have h := DFunLike.congr_fun (cd.toPoint_deltaT 𝕃 Γ.π (F cd)) (𝕃.cls _ _ x)
  simp only [AddMonoidHom.comp_apply] at h
  change 𝕃.σtail _ (cd.delta1 𝕃 (F cd) (𝕃.cls _ _ (Lconc.map (cd.res Γ.π ≫ cd.push) x))) ∈
    divTail p
  rw [𝕃.cls_map, ← h, ← forgetControl_comp_forgetInv, ← LowerLTheory.map_comp_apply,
    LowerLTheory.σtail_forget]
  exact theorem_6_3 𝕃 cd Γ _

/-- **`TransferDivisibility` for the pinned fibre signature.** -/
theorem transferDivisibility (𝕃 : LowerLTheory) : TransferDivisibility (fibreSignature 𝕃) :=
  transferDivisibility_of 𝕃 _

end

end HSFormal
