import HSFormal.WeakInputs
import HSFormal.Montgomery

/-!
# Montgomery's theorem from Newman's theorem for prime order

This file proves `HSFormal.pointwisePeriodicIsPeriodic_of_newmanPrimeOrder`: the published input
`HSFormal.PointwisePeriodicIsPeriodic` ([Mon37]) follows from `HSFormal.NewmanPrimeOrder`, used
only with *zero* displacement (Newman's second theorem, [Tao11, Thm 6]). The argument of
`HSFormal/Montgomery.lean` is repeated verbatim with `HSFormal.newman_rigidity'` in place of
`HSFormal.newman_rigidity`.

* `HSFormal.eq_of_iterate_eq_of_eqOn_open`: on a connected manifold, a continuous `H` with
  `H^[N] = id` (`N > 0`) that is the identity on a nonempty open set is the identity. Strong
  induction on `N`: for a prime `q ∣ N`, `H^[N/q]` is a homeomorphism of order dividing `q`
  fixing the open set, hence the identity by `NewmanPrimeOrder`, and `N/q < N`.
* `HSFormal.newman_rigidity'`: the same for a map restricting to a periodic map of a connected
  open subset `D` of a manifold.
-/

open Set Filter Topology

namespace HSFormal

/-- A continuous self-map `g` with `g^[k+1] = id`, as a homeomorphism (inverse `g^[k]`). -/
def homeomorphOfIterateEqId {X : Type*} [TopologicalSpace X] (g : X → X) (hg : Continuous g)
    (k : ℕ) (hper : ∀ x, g^[k + 1] x = x) : X ≃ₜ X where
  toFun := g
  invFun := g^[k]
  left_inv x := by rw [← Function.iterate_succ_apply g k x]; exact hper x
  right_inv x := by rw [← Function.iterate_succ_apply' g k x]; exact hper x
  continuous_toFun := hg
  continuous_invFun := hg.iterate k

/-- **Newman's second theorem for periodic maps** (from `NewmanPrimeOrder`, zero displacement):
on a connected manifold, a continuous `H` with `H^[N] = id` for some `N > 0` which is the
identity on a nonempty open set is the identity. -/
theorem eq_of_iterate_eq_of_eqOn_open (hN : NewmanPrimeOrder) {n : ℕ} {X : Type} [MetricSpace X]
    [SecondCountableTopology X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [ConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) {H : X → X} (hH : Continuous H)
    (hfix : ∀ x ∈ U, H x = x) : ∀ N : ℕ, 0 < N → (∀ x, H^[N] x = x) → ∀ x, H x = x := by
  obtain ⟨ε, hε, hNε⟩ := hN n X U hU hUne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hNpos hper
    by_cases h1 : N = 1
    · subst h1; exact hper
    obtain ⟨q, hq, r, rfl⟩ := Nat.exists_prime_and_dvd h1
    have hr : 0 < r := Nat.pos_of_mul_pos_left hNpos
    have hK : ∀ x, (H^[r])^[q] x = x := fun x => by
      rw [← Function.iterate_mul, mul_comm]; exact hper x
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq.pos).symm⟩
    have hKfix : ∀ x ∈ U, H^[r] x = x := fun x hx => Function.iterate_fixed (hfix x hx) r
    have hΦ := hNε (q' + 1) hq (homeomorphOfIterateEqId (H^[r]) (hH.iterate r) q' hK) hK
      (fun k x hx => by
        change dist ((H^[r])^[k] x) x < ε
        rw [Function.iterate_fixed (hKfix x hx) k, dist_self]
        exact hε)
    refine ih r ?_ hr hΦ
    have := hq.one_lt
    nlinarith

/-- **Newman's rigidity** (from `HSFormal.NewmanPrimeOrder`): a map `h` which restricts to a
periodic homeomorphism of a connected open set `D` and is the identity on a nonempty open subset
of `D` is the identity on `D`. Same statement as `HSFormal.newman_rigidity`. -/
theorem newman_rigidity' (hN : NewmanPrimeOrder) {n : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {D U : Set M} (hD : IsOpen D) (hDc : IsConnected D) (hU : IsOpen U)
    (hUD : (U ∩ D).Nonempty) {h : M → M} (hmaps : MapsTo h D D) (hcont : ContinuousOn h D)
    {m : ℕ} (hper : ∀ x ∈ D, h^[m + 1] x = x) (hfix : ∀ x ∈ U ∩ D, h x = x) :
    ∀ x ∈ D, h x = x := by
  set D' : TopologicalSpace.Opens M := ⟨D, hD⟩
  haveI : ConnectedSpace D' := isConnected_iff_connectedSpace.mp hDc
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : MetricSpace D' := TopologicalSpace.metrizableSpaceMetric D'
  let H : D' → D' := fun x => ⟨h x, hmaps x.2⟩
  have hHit : ∀ (k : ℕ) (x : D'), ((H^[k] x : D') : M) = h^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have hHper : ∀ x : D', H^[m + 1] x = x := fun x => Subtype.ext ((hHit _ x).trans (hper x x.2))
  have hHc : Continuous H := (hcont.domRestrict).subtype_mk _
  set U' : Set D' := Subtype.val ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hU'ne : U'.Nonempty := by
    obtain ⟨x, hxU, hxD⟩ := hUD
    exact ⟨⟨x, hxD⟩, hxU⟩
  have hid := eq_of_iterate_eq_of_eqOn_open hN (n := n) (X := D') hU' hU'ne hHc
    (fun x hx => Subtype.ext (hfix x ⟨hx, x.2⟩)) (m + 1) m.succ_pos hHper
  intro x hx
  exact congrArg Subtype.val (hid ⟨x, hx⟩)

section Montgomery

variable {M : Type} [TopologicalSpace M]

/-- **Local closedness** (Newman). If `f^[K+1] = id` near `y` and `y` is a limit of points near
which `f^[N+1] = id`, then `f^[N+1] = id` near `y`. -/
theorem mem_interior_perSet_of_mem_closure' (hN : NewmanPrimeOrder) {n : ℕ} [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M ≃ₜ M) {K N : ℕ} {y : M}
    (hyK : y ∈ interior (perSet f (K + 1)))
    (hyN : y ∈ closure (interior (perSet f (N + 1)))) :
    y ∈ interior (perSet f (N + 1)) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  set C := connectedComponentIn (interior (perSet f (K + 1))) y
  have hCo : IsOpen C := isOpen_interior.connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hyK
  have hyC : y ∈ C := mem_connectedComponentIn hyK
  have hCsub : C ⊆ interior (perSet f (K + 1)) := connectedComponentIn_subset _ _
  set g := f^[N + 1]
  have hgc : Continuous g := f.continuous.iterate _
  have hgy : g y = y :=
    (closure_minimal interior_subset (isClosed_perSet f (N + 1))) hyN
  have hgC : MapsTo g C C := by
    intro x hx
    have hsub : g '' C ⊆ C := by
      refine (hCc.isPreconnected.image g hgc.continuousOn).subset_connectedComponentIn
        ⟨y, hyC, hgy⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      exact iterate_mapsTo_interior_perSet f (K + 1) (N + 1) (hCsub hz)
    exact hsub (mem_image_of_mem g hx)
  have hfix := newman_rigidity' hN (n := n) hCo hCc isOpen_interior
      (by
        obtain ⟨z, hz⟩ := mem_closure_iff.1 hyN C hCo hyC
        exact ⟨z, hz.2, hz.1⟩)
      hgC hgc.continuousOn (m := K)
      (fun x hx => iterate_iterate_eq_of_mem_perSet f (N + 1) (interior_subset (hCsub hx)))
      (fun x hx => by have := interior_subset hx.1; exact this)
  have hCN : C ⊆ interior (perSet f (N + 1)) := interior_maximal (fun x hx => hfix x hx) hCo
  exact hCN hyC


/-- **Baire + Newman**: for a pointwise periodic homeomorphism, the period is bounded near every
point. -/
theorem boundedSet_eq_univ' (hN : NewmanPrimeOrder) {n : ℕ} [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M ≃ₜ M) (hf : ∀ x, ∃ k, 0 < k ∧ f^[k] x = x) : boundedSet f = univ := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  set O := boundedSet f
  by_contra hne
  obtain ⟨y₀, hy₀⟩ : (Oᶜ).Nonempty := by
    rw [nonempty_compl]; exact hne
  -- Baire on the closed set `Z = Oᶜ`.
  have hOo : IsOpen O := isOpen_iUnion fun _ => isOpen_interior
  set Z := Oᶜ
  have hZc : IsClosed Z := hOo.isClosed_compl
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Nonempty Z := ⟨⟨y₀, hy₀⟩⟩
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun k : ℕ => (Subtype.val ⁻¹' perSet f (k + 1) : Set Z))
    (fun k => (isClosed_perSet f (k + 1)).preimage continuous_subtype_val)
    (by
      refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
      obtain ⟨j, hj, hjz⟩ := hf z.1
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
      exact ⟨k, by simpa [perSet] using hjz⟩)
  obtain ⟨z, hz⟩ := hk
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_interior (s := (Subtype.val ⁻¹'
    perSet f (k + 1) : Set Z)))
  have hzV : z.1 ∈ V := by
    have : z ∈ Subtype.val ⁻¹' V := hV.symm ▸ hz
    exact this
  have hVZ : ∀ x ∈ V, x ∉ O → x ∈ perSet f (k + 1) := by
    intro x hxV hxO
    have : (⟨x, hxO⟩ : Z) ∈ interior (Subtype.val ⁻¹' perSet f (k + 1) : Set Z) := by
      rw [← hV]; exact hxV
    exact (interior_subset this : (⟨x, hxO⟩ : Z) ∈ (Subtype.val ⁻¹' perSet f (k + 1) : Set Z))
  -- the connected component `D` of `y` in `V' = int (O ∪ F_{k+1})`
  set y := z.1
  have hyO : y ∉ O := z.2
  set P := perSet f (k + 1)
  set V' := interior (O ∪ P)
  have hVV' : V ⊆ V' := interior_maximal (fun x hx => by
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · exact Or.inr (hVZ x hx hxO)) hVo
  have hyV' : y ∈ V' := hVV' hzV
  set g := f^[k + 1]
  have hgc : Continuous g := f.continuous.iterate _
  have hgy : g y = y := hVZ y hzV hyO
  have hgV' : MapsTo g V' V' :=
    (mapsTo_interior_of_mapsTo f ((mapsTo_boundedSet f).union_union (mapsTo_perSet f _))).iterate _
  have hV'Z : ∀ x ∈ V', x ∉ O → g x = x := by
    intro x hx hxO
    rcases interior_subset hx with h | h
    · exact absurd h hxO
    · exact h
  set D := connectedComponentIn V' y
  have hDo : IsOpen D := isOpen_interior.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hyV'
  have hyD : y ∈ D := mem_connectedComponentIn hyV'
  have hDsub : D ⊆ V' := connectedComponentIn_subset _ _
  have hgD : MapsTo g D D := by
    intro x hx
    have hsub : g '' D ⊆ D :=
      (hDc.isPreconnected.image g hgc.continuousOn).subset_connectedComponentIn
        ⟨y, hyD, hgy⟩ (by rintro _ ⟨w, hw, rfl⟩; exact hgV' (hDsub hw))
    exact hsub (mem_image_of_mem g hx)
  -- some point of `D ∩ O` is moved by `g`
  obtain ⟨w, hwD, hwO, hgw⟩ : ∃ w ∈ D, w ∈ O ∧ g w ≠ w := by
    by_contra hcon
    push Not at hcon
    have hDP : D ⊆ interior P := interior_maximal (fun x hx => by
      by_cases hxO : x ∈ O
      · exact hcon x hx hxO
      · exact hV'Z x (hDsub hx) hxO) hDo
    exact hyO (interior_perSet_subset_boundedSet f (Nat.succ_pos k) (hDP hyD))
  obtain ⟨m, hwm⟩ := mem_iUnion.1 hwO
  set Ω := D ∩ interior (perSet f (m + 1))
  have hΩo : IsOpen Ω := hDo.inter isOpen_interior
  have hwΩ : w ∈ Ω := ⟨hwD, hwm⟩
  have hgΩ : MapsTo g Ω Ω := fun x hx =>
    ⟨hgD hx.1, iterate_mapsTo_interior_perSet f (m + 1) (k + 1) hx.2⟩
  have hΩper : ∀ x ∈ Ω, g^[m + 1] x = x := fun x hx =>
    iterate_iterate_eq_of_mem_perSet f (k + 1) (interior_subset hx.2)
  -- on the frontier of `Ω` inside `D`, `g` is the identity (local closedness)
  have hfront : ∀ x ∈ D, x ∈ closure Ω → x ∉ Ω → g x = x := by
    intro x hxD hxcl hxΩ
    by_cases hxO : x ∈ O
    · obtain ⟨K, hK⟩ := mem_iUnion.1 hxO
      have := mem_interior_perSet_of_mem_closure' hN (n := n) f hK
        (closure_mono inter_subset_right hxcl)
      exact absurd ⟨hxD, this⟩ hxΩ
    · exact hV'Z x (hDsub hxD) hxO
  -- the periodic homeomorphism `h` of `D`: `g` on `Ω`, the identity elsewhere
  classical
  set h : M → M := Ω.piecewise g id
  have hhΩ : ∀ x ∈ Ω, h x = g x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hhnΩ : ∀ x ∉ Ω, h x = x := fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx
  have hhc : ContinuousOn h D := by
    refine ContinuousOn.piecewise (fun x hx => ?_) hgc.continuousOn continuousOn_id
    rw [hΩo.frontier_eq] at hx
    exact hfront x hx.1 hx.2.1 hx.2.2
  have hhD : MapsTo h D D := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hhΩ x hxΩ]; exact hgD hx
    · rw [hhnΩ x hxΩ]; exact hx
  have hhit : ∀ j : ℕ, ∀ x ∈ Ω, h^[j] x = g^[j] x := by
    intro j
    induction j with
    | zero => intro x _; rfl
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x hx,
        hhΩ _ (hgΩ.iterate j hx)]
  have hhper : ∀ x ∈ D, h^[m + 1] x = x := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hhit _ x hxΩ]; exact hΩper x hxΩ
    · exact Function.iterate_fixed (hhnΩ x hxΩ) _
  by_cases hdense : D ⊆ closure Ω
  · -- then `g^[m+1] = id` on `D`, so `y ∈ O`
    have hDP : D ⊆ interior (perSet f ((k + 1) * (m + 1))) := interior_maximal (fun x hx => by
      change f^[(k + 1) * (m + 1)] x = x
      rw [Function.iterate_mul]
      by_cases hxΩ : x ∈ Ω
      · exact hΩper x hxΩ
      · exact Function.iterate_fixed (hfront x hx (hdense hx) hxΩ) _) hDo
    exact hyO (interior_perSet_subset_boundedSet f (Nat.mul_pos (Nat.succ_pos k)
      (Nat.succ_pos m)) (hDP hyD))
  · -- otherwise `h` is the identity on the open set `D \ closure Ω`: Newman's rigidity
    obtain ⟨x, hxD, hxcl⟩ := not_subset.1 hdense
    have hid := newman_rigidity' hN (n := n) hDo hDc isClosed_closure.isOpen_compl
      ⟨x, hxcl, hxD⟩ hhD hhc hhper
      (fun x hx => hhnΩ x fun hxΩ => hx.1 (subset_closure hxΩ))
    exact hgw ((hhΩ w hwΩ).symm.trans (hid w hwD))

end Montgomery

/-- **Montgomery's theorem from Newman's theorem for prime order.** `NewmanPrimeOrder` (used only
with zero displacement on an open set) implies that a pointwise periodic homeomorphism of a
connected manifold without boundary is periodic. -/
theorem pointwisePeriodicIsPeriodic_of_newmanPrimeOrder (h : NewmanPrimeOrder) :
    PointwisePeriodicIsPeriodic := by
  intro n M _ _ _ _ _ f hf
  have hO := boundedSet_eq_univ' h (n := n) f hf
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, one_pos, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨N, hN⟩ := mem_iUnion.1 (hO.symm ▸ mem_univ x₀ : x₀ ∈ boundedSet f)
  have hcl : IsClopen (interior (perSet f (N + 1))) := by
    refine ⟨closure_subset_iff_isClosed.1 fun y hy => ?_, isOpen_interior⟩
    obtain ⟨K, hK⟩ := mem_iUnion.1 (hO.symm ▸ mem_univ y : y ∈ boundedSet f)
    exact mem_interior_perSet_of_mem_closure' h (n := n) f hK hy
  have huniv := hcl.eq_univ ⟨x₀, hN⟩
  refine ⟨N + 1, Nat.succ_pos N, fun x => ?_⟩
  have hx : x ∈ interior (perSet f (N + 1)) := huniv.symm ▸ mem_univ x
  exact (interior_subset hx : x ∈ perSet f (N + 1))

end HSFormal
