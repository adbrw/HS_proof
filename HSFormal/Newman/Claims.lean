import HSFormal.Newman.TransferStatement

/-!
# N8. Claims 1 and 2′ (Newman blueprint, module N8)

Throughout, `𝔼 = EuclideanSpace ℝ (Fin (m + 1))`, `V ⊆ 𝔼` is open and `g : 𝔼 → 𝔼` maps `V`
to itself, is continuous on `V` and satisfies `g^[q] = id` on `V` for a prime `q`. The transfer
vanishing lemma (N7, blueprint §2.4) enters as the hypothesis `hT : DegreeEqZeroOfFree`
(`HSFormal/Newman/TransferStatement.lean`).

* `avg q g z = q⁻¹ ∑_{k<q} g^[k] z`, the averaging map (§2.5), and
  `avgPol q g a z = a + (q⁻¹ ∑_{k<q} ‖g^[k] z - a‖) • v / ‖v‖` with `v = ∑_{k<q} (g^[k] z - a)`,
  the polar averaging map (§2.6). Both are `g`-invariant (`avg_apply_eq`, `avgPol_apply_eq`)
  and are the identity on fixed points (`avg_eq_self_of_fixed`, `avgPol_eq_self_of_fixed`).
* **Claim 1** `fixed_of_small_orbits`: if every orbit of a point of `B̄(c, r) ⊆ V` stays within
  `r / 32` of it, then `g = id` on `B(c, r / 2)`.
* **Claim 2′** `false_of_fixed_ball_touching`: a pointwise fixed closed ball `B̄(a, r) ⊆ V`
  cannot touch, at a point `b` of its boundary sphere, the closure of the non-fixed locus.

## Deviations from the blueprint

* `R` (§2.6) is only required to satisfy `R ≤ r` (instead of `R ≤ r / 2`): `v ≠ 0` is proved by
  the reverse triangle inequality `‖v - q (b - a)‖ < q R ≤ q r = ‖q (b - a)‖` rather than by an
  inner product estimate.
* The frontier of `W* = ⋃_{k<q} g^[k] B(b, ρ)` is replaced by `C* \ W*` with
  `C* = ⋃_{k<q} g^[k] B̄(b, ρ)` compact: `b ∉ A (C* \ W*)` (a fixed point of `C* \ W*` is `≠ b`
  since `b ∈ W*`; a non-fixed one is mapped outside `B̄(a, r)`), and the compactness of the
  fibres of `A` over `B(b, s)` in `W*` follows.
* Degree one at `y'` is obtained from the straight-line homotopy on `W* ∩ B(a, r)`, where
  `A = id`, and (D-loc).
-/

open Set Function Metric Topology Filter

namespace HSFormal.Newman

/-! ### Generalities -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reindexing a sum over an orbit of period dividing `q`. -/
lemma sum_range_iterate_comp {X M : Type*} [AddCancelCommMonoid M] {g : X → X} {q : ℕ} {z : X}
    (hz : g^[q] z = z) (F : X → M) :
    ∑ k ∈ Finset.range q, F (g^[k] (g z)) = ∑ k ∈ Finset.range q, F (g^[k] z) := by
  have h1 := Finset.sum_range_succ' (fun k => F (g^[k] z)) q
  have h2 := Finset.sum_range_succ (fun k => F (g^[k] z)) q
  simp only [iterate_succ_apply, iterate_zero_apply] at h1
  simp only [hz] at h2
  exact add_right_cancel (h1.symm.trans h2)

omit [NormedSpace ℝ E] in
/-- Compactness of `{w : W | A w ∈ S}` from a compact `C` on which `A` is continuous and which
has the same points over `S` as `W`. -/
lemma isCompact_setOf_mem_of_iff {W C S : Set E} {A : E → E} (hC : IsCompact C)
    (hA : ContinuousOn A C) (hS : IsClosed S) (hWC : ∀ z, A z ∈ S → (z ∈ W ↔ z ∈ C)) :
    IsCompact {w : W | A w ∈ S} := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  have : Subtype.val '' {w : W | A w ∈ S} = C ∩ A ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hWC w hw).1 w.2, hw⟩
    · rintro ⟨hzC, hzS⟩
      exact ⟨⟨z, (hWC z hzS).2 hzC⟩, hzS, rfl⟩
  rw [this]
  exact hC.of_isClosed_subset (hA.preimage_isClosed_of_isClosed hC.isClosed hS) inter_subset_left

omit [NormedSpace ℝ E] in
lemma isCompact_fibre_of_iff {W C : Set E} {A : E → E} {y : E} (hC : IsCompact C)
    (hA : ContinuousOn A C) (hWC : ∀ z, A z = y → (z ∈ W ↔ z ∈ C)) :
    IsCompact {w : W | A w = y} :=
  isCompact_setOf_mem_of_iff (S := {y}) hC hA isClosed_singleton hWC

/-! #### The averaging map -/

/-- The averaging map `z ↦ q⁻¹ ∑_{k<q} g^[k] z` (§2.5). -/
noncomputable def avg (q : ℕ) (g : E → E) (z : E) : E :=
  (q : ℝ)⁻¹ • ∑ k ∈ Finset.range q, g^[k] z

lemma continuousOn_avg {q : ℕ} {V : Set E} {g : E → E} (hgV : MapsTo g V V)
    (hgc : ContinuousOn g V) : ContinuousOn (avg q g) V :=
  (continuousOn_finsetSum _ fun k _ => hgc.iterate hgV k).const_smul _

lemma avg_apply_eq {q : ℕ} {g : E → E} {z : E} (hz : g^[q] z = z) : avg q g (g z) = avg q g z := by
  unfold avg
  rw [sum_range_iterate_comp hz (fun x => x)]

lemma smul_nsmul_inv_eq {q : ℕ} (hq : 0 < q) (x : E) : (q : ℝ)⁻¹ • (q • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hq.ne'),
    one_smul]

lemma avg_eq_self_of_fixed {q : ℕ} (hq : 0 < q) {g : E → E} {z : E} (hz : g z = z) :
    avg q g z = z := by
  simp only [avg, iterate_fixed hz, Finset.sum_const, Finset.card_range]
  exact smul_nsmul_inv_eq hq z

lemma dist_avg_le {q : ℕ} (hq : 0 < q) {g : E → E} {z : E} {δ : ℝ}
    (hδ : ∀ k, dist (g^[k] z) z ≤ δ) : dist (avg q g z) z ≤ δ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : avg q g z - z = (q : ℝ)⁻¹ • ∑ k ∈ Finset.range q, (g^[k] z - z) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub,
      smul_nsmul_inv_eq hq]
    rfl
  rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hq'.le)]
  calc (q : ℝ)⁻¹ * ‖∑ k ∈ Finset.range q, (g^[k] z - z)‖
      ≤ (q : ℝ)⁻¹ * ∑ k ∈ Finset.range q, δ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [← dist_eq_norm]
        exact hδ k
    _ = δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hq'.ne', one_mul]

/-! #### The polar averaging map -/

/-- The polar averaging map `z ↦ a + (q⁻¹ ∑_{k<q} ‖g^[k] z - a‖) • v / ‖v‖`, where
`v = ∑_{k<q} (g^[k] z - a)` (§2.6). -/
noncomputable def avgPol (q : ℕ) (g : E → E) (a z : E) : E :=
  a + ((q : ℝ)⁻¹ * ∑ k ∈ Finset.range q, ‖g^[k] z - a‖) •
    (‖∑ k ∈ Finset.range q, (g^[k] z - a)‖⁻¹ • ∑ k ∈ Finset.range q, (g^[k] z - a))

lemma avgPol_apply_eq {q : ℕ} {g : E → E} {a z : E} (hz : g^[q] z = z) :
    avgPol q g a (g z) = avgPol q g a z := by
  unfold avgPol
  rw [sum_range_iterate_comp hz (fun x => ‖x - a‖), sum_range_iterate_comp hz (fun x => x - a)]

lemma avgPol_eq_self_of_fixed {q : ℕ} (hq : 0 < q) {g : E → E} {a z : E} (hz : g z = z) :
    avgPol q g a z = z := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [avgPol, iterate_fixed hz, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_of_nonneg hq'.le, smul_smul, smul_smul]
  rcases eq_or_ne (z - a) 0 with h | h
  · rw [h, smul_zero, add_zero, ← sub_eq_zero.1 h]
  · have hn : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.2 h
    have : (q : ℝ)⁻¹ * (q * ‖z - a‖) * (q * ‖z - a‖)⁻¹ * q = 1 := by
      field_simp
    rw [this, one_smul, add_sub_cancel]

lemma sum_iterate_sub_ne_zero {q : ℕ} (hq : 0 < q) {g : E → E} {a b z : E} {R : ℝ}
    (hR : R ≤ dist b a) (h : ∀ k < q, dist (g^[k] z) b < R) :
    ∑ k ∈ Finset.range q, (g^[k] z - a) ≠ 0 := by
  intro hv
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : ∑ k ∈ Finset.range q, (g^[k] z - a) - (q : ℝ) • (b - a) =
      ∑ k ∈ Finset.range q, (g^[k] z - b) := by
    have : ∑ k ∈ Finset.range q, (g^[k] z - b) =
        ∑ k ∈ Finset.range q, ((g^[k] z - a) - (b - a)) :=
      Finset.sum_congr rfl fun k _ => by abel
    rw [this, Finset.sum_sub_distrib (fun k => g^[k] z - a) (fun _ => b - a), Finset.sum_const,
      Finset.card_range, Nat.cast_smul_eq_nsmul]
  have h1 : ‖∑ k ∈ Finset.range q, (g^[k] z - b)‖ < q * R := by
    refine (norm_sum_le _ _).trans_lt ?_
    calc ∑ k ∈ Finset.range q, ‖g^[k] z - b‖ < ∑ k ∈ Finset.range q, R :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hq.ne') fun k hk => by
            rw [← dist_eq_norm]; exact h k (Finset.mem_range.1 hk)
      _ = q * R := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← e, hv, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hq'.le, ← dist_eq_norm] at h1
  nlinarith

lemma continuousOn_avgPol {q : ℕ} {V S : Set E} {g : E → E} (hgV : MapsTo g V V)
    (hgc : ContinuousOn g V) (hSV : S ⊆ V) (a : E)
    (hv : ∀ z ∈ S, ∑ k ∈ Finset.range q, (g^[k] z - a) ≠ 0) :
    ContinuousOn (avgPol q g a) S := by
  have hit : ∀ k, ContinuousOn (g^[k]) S := fun k => (hgc.iterate hgV k).mono hSV
  have hsum : ContinuousOn (fun z => ∑ k ∈ Finset.range q, (g^[k] z - a)) S :=
    continuousOn_finsetSum _ fun k _ => (hit k).sub continuousOn_const
  have hnorm : ContinuousOn (fun z => ∑ k ∈ Finset.range q, ‖g^[k] z - a‖) S :=
    continuousOn_finsetSum _ fun k _ => ((hit k).sub continuousOn_const).norm
  refine continuousOn_const.add ((continuousOn_const.mul hnorm).smul ?_)
  exact (hsum.norm.inv₀ fun z hz => norm_ne_zero_iff.2 (hv z hz)).smul hsum

lemma dist_avgPol_eq {q : ℕ} {g : E → E} {a z : E}
    (hv : ∑ k ∈ Finset.range q, (g^[k] z - a) ≠ 0) :
    dist (avgPol q g a z) a = (q : ℝ)⁻¹ * ∑ k ∈ Finset.range q, ‖g^[k] z - a‖ := by
  rw [dist_eq_norm, avgPol, add_sub_cancel_left, norm_smul, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hv), mul_one, Real.norm_of_nonneg]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg q))
    (Finset.sum_nonneg fun k _ => norm_nonneg _)

lemma lt_dist_avgPol {q : ℕ} (hq : 0 < q) {g : E → E} {a z : E} {r : ℝ}
    (hv : ∑ k ∈ Finset.range q, (g^[k] z - a) ≠ 0) (h : ∀ k < q, r < dist (g^[k] z) a) :
    r < dist (avgPol q g a z) a := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [dist_avgPol_eq hv]
  have : ∑ k ∈ Finset.range q, r < ∑ k ∈ Finset.range q, ‖g^[k] z - a‖ :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hq.ne') fun k hk => by
      rw [← dist_eq_norm]; exact h k (Finset.mem_range.1 hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  rw [lt_inv_mul_iff₀ hq']
  exact this

end General

/-! ### Claim 1 -/

section Claims

variable {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- **Claim 1** (§2.5). Let `g` be continuous on the open `V ⊆ 𝔼`, with `g (V) ⊆ V` and
`g^[q] = id` on `V` for a prime `q`. If `B̄(c, r) ⊆ V` and every point of `B̄(c, r)` is moved by at
most `r / 32` by every iterate of `g`, then `g` fixes `B(c, r / 2)` pointwise. -/
theorem fixed_of_small_orbits (hT : DegreeEqZeroOfFree) {q : ℕ} (hq : q.Prime) {V : Set 𝔼}
    (hV : IsOpen V) {g : 𝔼 → 𝔼} (hgV : MapsTo g V V) (hgc : ContinuousOn g V)
    (hper : ∀ z ∈ V, g^[q] z = z) {c : 𝔼} {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ V)
    (hsmall : ∀ z ∈ closedBall c r, ∀ k, dist (g^[k] z) z ≤ r / 32) :
    ∀ y ∈ ball c (r / 2), g y = y := by
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : 0 < q := hq.pos
  intro y hy
  by_contra hgy
  have hyc : dist y c < r / 2 := mem_ball.1 hy
  have hbV : ball c r ⊆ V := ball_subset_closedBall.trans hball
  have hAc : ContinuousOn (avg q g) V := continuousOn_avg hgV hgc
  have hAnear : ∀ z ∈ closedBall c r, dist (avg q g z) z ≤ r / 32 := fun z hz =>
    dist_avg_le hq0 (hsmall z hz)
  -- the fibre over `y` in `B(c, r)` lies in `B̄(c, 17 r / 32)`
  have hfibc : ∀ z ∈ ball c r, avg q g z = y → dist z c < 17 * r / 32 := by
    intro z hz hAz
    have h1 := hAnear z (ball_subset_closedBall hz)
    rw [hAz, dist_comm] at h1
    have h2 := dist_triangle z y c
    linarith
  have hKball : IsCompact {w : ball c r | avg q g w = y} :=
    isCompact_fibre_of_iff (C := closedBall c (17 * r / 32)) (isCompact_closedBall _ _)
      (hAc.mono ((closedBall_subset_closedBall (by linarith)).trans hball)) fun z hz =>
        ⟨fun h => mem_closedBall.2 (hfibc z h hz).le,
          fun h => closedBall_subset_ball (by linarith) h⟩
  -- degree one on `B(c, r)` (DEG1 with `r' = 3 r / 4`)
  have hdeg1 : degree (ZMod q) isOpen_ball (avg q g) (hAc.mono hbV) y hKball = 1 := by
    refine degree_eq_one_of_segment (r' := 3 * r / 4) (by linarith) (by linarith) ?_ hKball
    intro z hz1 hz2 t ht heq
    have hzn := hAnear z (mem_closedBall.2 hz2.le)
    have hyz : dist y z ≤ r / 32 := by
      rw [← heq, dist_eq_norm,
        show (1 - t) • z + t • avg q g z - z = t • (avg q g z - z) by module, norm_smul,
        Real.norm_of_nonneg ht.1]
      rw [dist_eq_norm] at hzn
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hzn
    have h2 := dist_triangle z y c
    rw [dist_comm z y] at h2
    linarith
  -- the free invariant open set `W = (⋂_{k<q} g^{-k} B(c, 3r/4)) \ Fix g`
  have hW₀ : IsOpen {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ ball c (3 * r / 4)} :=
    isOpen_setOf_iterate_mem hV hgV hgc isOpen_ball q
  have hgW₀ : MapsTo g {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ ball c (3 * r / 4)}
      {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ ball c (3 * r / 4)} :=
    mapsTo_setOf_iterate_mem hgV hper hq0 _
  have hW₀V : {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ ball c (3 * r / 4)} ⊆ V := fun z hz => hz.1
  have hinjg : InjOn g V := by
    simpa using injOn_iterate (p := q) hgV hper 1
  generalize hW₀def : {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ ball c (3 * r / 4)} = W₀ at hW₀ hgW₀ hW₀V
  have hW : IsOpen (W₀ \ {z | g z = z}) := isOpen_diff_fixedPoints hW₀ (hgc.mono hW₀V)
  have hgW : MapsTo g (W₀ \ {z | g z = z}) (W₀ \ {z | g z = z}) :=
    mapsTo_diff_fixedPoints hgW₀ (hinjg.mono hW₀V)
  have hWV : W₀ \ {z | g z = z} ⊆ V := sdiff_subset.trans hW₀V
  have hWb : W₀ \ {z | g z = z} ⊆ ball c (3 * r / 4) := by
    intro z hz
    have := hz.1
    rw [← hW₀def] at this
    exact this.2 0 hq0
  have hfibW : ∀ w ∈ ball c r, avg q g w = y → w ∈ W₀ \ {z | g z = z} := by
    intro w hw hAw
    have hwc := hfibc w hw hAw
    refine ⟨?_, fun hgw => hgy ?_⟩
    · rw [← hW₀def]
      refine ⟨hbV hw, fun k _ => mem_ball.2 ?_⟩
      have h1 := hsmall w (ball_subset_closedBall hw) k
      have h2 := dist_triangle (g^[k] w) w c
      linarith
    · have hwy : w = y := (avg_eq_self_of_fixed hq0 hgw).symm.trans hAw
      exact hwy ▸ hgw
  generalize hWdef : W₀ \ {z | g z = z} = W at hW hgW hWV hWb hfibW
  have hfree : ∀ w ∈ W, g w ≠ w := by
    rw [← hWdef]; exact fun w hw => hw.2
  have hperW : ∀ w ∈ W, g^[q] w = w := fun w hw => hper w (hWV hw)
  have hgcW : ContinuousOn g W := hgc.mono hWV
  -- local degrees of the iterates are one (LD1 on `V`, then D-loc)
  have hldeg : ∀ j, 0 < j → j < q → ∀ w (hw : w ∈ W),
      ldeg (ZMod q) hW (g^[j]) (hgcW.iterate hgW j) (injOn_iterate hgW hperW j) w hw = 1 := by
    intro j _ _ w hw
    have hwc : dist w c < 3 * r / 4 := mem_ball.1 (hWb hw)
    have hcb : closedBall w (r / 4) ⊆ closedBall c r := fun z hz => by
      have h1 := mem_closedBall.1 hz
      have h2 := dist_triangle z w c
      exact mem_closedBall.2 (by linarith)
    have h1 : ldeg (ZMod q) hV (g^[j]) (hgc.iterate hgV j) (injOn_iterate hgV hper j) w
        (hWV hw) = 1 :=
      ldeg_eq_one_of_dist_le (by positivity) (hcb.trans hball)
        (fun z hz => (hsmall z (hcb hz) j).trans (by linarith)) (hWV hw)
    rw [← h1]
    exact degree_congr_open (hW := hV) (hA := hgc.iterate hgV j) hW hWV _ _
      fun z hz hzw => (injOn_iterate hgV hper j hz (hWV hw) hzw) ▸ hw
  have hWball : W ⊆ ball c r := hWb.trans (ball_subset_ball (by linarith))
  have hKW : IsCompact {w : W | avg q g w = y} := isCompact_fibre_of_subset hWball hfibW hKball
  have h0 := hT q hW hgW hgcW hperW hfree hldeg (hAc.mono hWV)
    (fun w hw => avg_apply_eq (hper w (hWV hw))) hKW
  have h1 := degree_congr_open (R := ZMod q) (hW := isOpen_ball) (hA := hAc.mono hbV) hW hWball
    hKball hKW hfibW
  rw [hdeg1] at h1
  exact zero_ne_one (h0.symm.trans h1)

/-! ### Claim 2′ -/

/-- **Claim 2′** (§2.6). Let `g` be as in Claim 1 and let `B̄(a, r) ⊆ V` be pointwise fixed. Then
no point `b` of the sphere `S(a, r)` is a limit of non-fixed points. -/
theorem false_of_fixed_ball_touching (hT : DegreeEqZeroOfFree) {q : ℕ} (hq : q.Prime)
    {V : Set 𝔼} (hV : IsOpen V) {g : 𝔼 → 𝔼} (hgV : MapsTo g V V) (hgc : ContinuousOn g V)
    (hper : ∀ z ∈ V, g^[q] z = z) {a b : 𝔼} {r : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ V)
    (hfix : ∀ z ∈ closedBall a r, g z = z) (hb : b ∈ sphere a r)
    (hacc : ∀ s > 0, ∃ z ∈ V ∩ ball b s, g z ≠ z) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : 0 < q := hq.pos
  have hbV : b ∈ V := hball (sphere_subset_closedBall hb)
  have hgb : g b = b := hfix b (sphere_subset_closedBall hb)
  have hba : dist b a = r := mem_sphere.1 hb
  have hinjg : InjOn g V := by
    simpa using injOn_iterate (p := q) hgV hper 1
  -- the radius `R`
  obtain ⟨R₀, hR₀, hR₀V⟩ := Metric.isOpen_iff.1 hV b hbV
  obtain ⟨R, hR, hRR₀, hRr⟩ : ∃ R, 0 < R ∧ R ≤ R₀ ∧ R ≤ r :=
    ⟨min R₀ r, lt_min hR₀ hr, min_le_left _ _, min_le_right _ _⟩
  have hRV : ball b R ⊆ V := (ball_subset_ball hRR₀).trans hR₀V
  -- the radius `ρ`: `g^[k] B̄(b, ρ) ⊆ B(b, R)` for `k < q`
  have hev : ∀ᶠ z in 𝓝 b, ∀ k ∈ Iio q, g^[k] z ∈ ball b R := by
    rw [(finite_Iio q).eventually_all]
    intro k _
    have hc : ContinuousAt (g^[k]) b := (hgc.iterate hgV k).continuousAt (hV.mem_nhds hbV)
    have hk : ball b R ∈ 𝓝 (g^[k] b) := by
      rw [iterate_fixed hgb k]; exact ball_mem_nhds b hR
    exact hc.preimage_mem_nhds hk
  obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.eventually_nhds_iff.1 hev
  have hρ : 0 < ρ₀ / 2 := by positivity
  have hρmem : ∀ z ∈ closedBall b (ρ₀ / 2), ∀ k < q, g^[k] z ∈ ball b R := fun z hz k hk =>
    hρ₀' (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)) k hk
  generalize ρ₀ / 2 = ρ at hρ hρmem
  have hρV : closedBall b ρ ⊆ V := fun z hz => hRV (by simpa using hρmem z hz 0 hq0)
  have hbρV : ball b ρ ⊆ V := ball_subset_closedBall.trans hρV
  -- `C* = ⋃_{k<q} g^[k] B̄(b, ρ)` and `W* = ⋃_{k<q} g^[k] B(b, ρ)`
  have hCR : (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ) ⊆ ball b R := by
    intro z hz
    obtain ⟨k, hk, x, hx, rfl⟩ := mem_iUnion₂.1 hz
    exact hρmem x hx k hk
  have hCV : (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ) ⊆ V := hCR.trans hRV
  have hWsC : (⋃ k ∈ Iio q, g^[k] '' ball b ρ) ⊆ ⋃ k ∈ Iio q, g^[k] '' closedBall b ρ :=
    iUnion₂_mono fun k _ => image_mono ball_subset_closedBall
  have hCc : IsCompact (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ) :=
    (finite_Iio q).isCompact_biUnion fun k _ =>
      (isCompact_closedBall b ρ).image_of_continuousOn ((hgc.iterate hgV k).mono hρV)
  have hgC : MapsTo g (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ)
      (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ) := mapsTo_iUnion_image_iterate hper hρV
  have hgWs : MapsTo g (⋃ k ∈ Iio q, g^[k] '' ball b ρ) (⋃ k ∈ Iio q, g^[k] '' ball b ρ) :=
    mapsTo_iUnion_image_iterate hper hbρV
  have hWso : IsOpen (⋃ k ∈ Iio q, g^[k] '' ball b ρ) :=
    isOpen_biUnion fun k _ => isOpen_image_iterate hgV hgc hper hV isOpen_ball hbρV k
  have hbWs : ball b ρ ⊆ ⋃ k ∈ Iio q, g^[k] '' ball b ρ := fun z hz =>
    mem_iUnion₂.2 ⟨0, hq0, z, hz, rfl⟩
  have hWsconn : IsPreconnected (⋃ k ∈ Iio q, g^[k] '' ball b ρ) := by
    refine isPreconnected_of_forall b fun z hz => ?_
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
    exact ⟨g^[k] '' ball b ρ, subset_biUnion_of_mem (u := fun k => g^[k] '' ball b ρ) hk,
      ⟨b, mem_ball_self hρ, iterate_fixed hgb k⟩, hzk,
      (convex_ball b ρ).isPreconnected.image _ ((hgc.iterate hgV k).mono hbρV)⟩
  generalize hCdef : (⋃ k ∈ Iio q, g^[k] '' closedBall b ρ) = C at hCR hCV hWsC hCc hgC
  generalize hWsdef : (⋃ k ∈ Iio q, g^[k] '' ball b ρ) = Ws at hWsC hgWs hWso hbWs hWsconn
  have hWsV : Ws ⊆ V := hWsC.trans hCV
  have hCorb : ∀ z ∈ C, ∀ k < q, dist (g^[k] z) b < R := fun z hz k _ =>
    mem_ball.1 (hCR (hgC.iterate k hz))
  -- the polar averaging map `A`
  have hv : ∀ z ∈ C, ∑ k ∈ Finset.range q, (g^[k] z - a) ≠ 0 := fun z hz =>
    sum_iterate_sub_ne_zero hq0 (hRr.trans hba.ge) (hCorb z hz)
  have hAc : ContinuousOn (avgPol q g a) C := continuousOn_avgPol hgV hgc hCV a hv
  have hAfix : ∀ z, g z = z → avgPol q g a z = z := fun z hz => avgPol_eq_self_of_fixed hq0 hz
  have hAfar : ∀ z ∈ C, g z ≠ z → r < dist (avgPol q g a z) a := by
    intro z hz hgz
    refine lt_dist_avgPol hq0 (hv z hz) fun k hk => ?_
    by_contra hle
    have hfk : g (g^[k] z) = g^[k] z := hfix _ (mem_closedBall.2 (not_lt.1 hle))
    have h1 : g^[q - k] (g^[k] z) = z := iterate_sub_iterate hper hk.le (hCV hz)
    rw [iterate_fixed hfk] at h1
    exact hgz (h1 ▸ hfk)
  -- avoiding `C* \ W*`
  have hK₀ : IsCompact (avgPol q g a '' (C \ Ws)) :=
    (hCc.diff hWso).image_of_continuousOn (hAc.mono sdiff_subset)
  have hbK₀ : b ∉ avgPol q g a '' (C \ Ws) := by
    rintro ⟨z, ⟨hzC, hzWs⟩, hAz⟩
    by_cases hgz : g z = z
    · rw [hAfix z hgz] at hAz
      exact hzWs (hAz ▸ hbWs (mem_ball_self hρ))
    · have := hAfar z hzC hgz
      rw [hAz, hba] at this
      exact lt_irrefl _ this
  obtain ⟨s₀, hs₀, hs₀K⟩ := Metric.isOpen_iff.1 hK₀.isClosed.isOpen_compl b hbK₀
  obtain ⟨s, hs, hss₀, hsρ, hsr⟩ : ∃ s, 0 < s ∧ s ≤ s₀ ∧ s ≤ ρ ∧ s ≤ r :=
    ⟨min (min s₀ ρ) r, lt_min (lt_min hs₀ hρ) hr, (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  have havoid : ∀ z ∈ C, avgPol q g a z ∈ ball b s → z ∈ Ws := by
    intro z hzC hAz
    by_contra hzWs
    exact hs₀K (ball_subset_ball hss₀ hAz) ⟨z, ⟨hzC, hzWs⟩, rfl⟩
  have hcomp : ∀ S, IsClosed S → S ⊆ ball b s → IsCompact {w : Ws | avgPol q g a w ∈ S} :=
    fun S hS hSs => isCompact_setOf_mem_of_iff hCc hAc hS fun z hz =>
      ⟨fun h => hWsC h, fun h => havoid z h (hSs hz)⟩
  have hAWs : ContinuousOn (avgPol q g a) Ws := hAc.mono hWsC
  -- (SEG) the degree is constant on `B(b, s)`
  have hconst : ∀ y₁ ∈ ball b s, ∀ y₂ ∈ ball b s, ∀ (hK₁ : IsCompact {w : Ws | avgPol q g a w = y₁})
      (hK₂ : IsCompact {w : Ws | avgPol q g a w = y₂}),
      degree (ZMod q) hWso (avgPol q g a) hAWs y₁ hK₁ =
        degree (ZMod q) hWso (avgPol q g a) hAWs y₂ hK₂ := by
    intro y₁ h₁ y₂ h₂ hK₁ hK₂
    refine degree_eq_of_segment (hcomp _ ?_ ((convex_ball b s).segment_subset h₁ h₂)) hK₁ hK₂
    rw [← convexHull_pair]
    exact (toFinite _).isClosed_convexHull ℝ
  -- the point `y' ∈ B(a, r) ∩ B(b, s)`
  have hy'b : dist (b + (s / 2 / r) • (a - b)) b = s / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm, dist_comm, hba,
      Real.norm_of_nonneg (by positivity)]
    field_simp
  have hy'a : dist (b + (s / 2 / r) • (a - b)) a = r - s / 2 := by
    rw [dist_eq_norm, show b + (s / 2 / r) • (a - b) - a = (1 - s / 2 / r) • (b - a) by module,
      norm_smul, ← dist_eq_norm b a, hba, Real.norm_of_nonneg]
    · field_simp
    · rw [sub_nonneg, div_le_one hr]; linarith
  generalize b + (s / 2 / r) • (a - b) = y' at hy'b hy'a
  have hy'bs : y' ∈ ball b s := mem_ball.2 (by linarith)
  have hy'ar : y' ∈ ball a r := mem_ball.2 (by linarith)
  have hy'Ws : y' ∈ Ws := hbWs (ball_subset_ball hsρ hy'bs)
  -- degree one at `y'`
  have hO : IsOpen (Ws ∩ ball a r) := hWso.inter isOpen_ball
  have hAO : ∀ z ∈ Ws ∩ ball a r, avgPol q g a z = z := fun z hz =>
    hAfix z (hfix z (ball_subset_closedBall hz.2))
  have hKO : IsCompact {w : (Ws ∩ ball a r : Set 𝔼) | avgPol q g a w = y'} :=
    isCompact_fibre_of_iff (C := {y'}) isCompact_singleton (continuousOn_singleton _ _)
      fun z hz => ⟨fun h => by rw [← hz, hAO z h]; rfl, fun h => (mem_singleton_iff.1 h) ▸
        ⟨hy'Ws, hy'ar⟩⟩
  have hfibO : ∀ w ∈ Ws, avgPol q g a w = y' → w ∈ Ws ∩ ball a r := by
    intro w hw hAw
    by_cases hgw : g w = w
    · rw [hAfix w hgw] at hAw
      exact hAw ▸ ⟨hy'Ws, hy'ar⟩
    · have := hAfar w (hWsC hw) hgw
      rw [hAw, hy'a] at this
      linarith
  have hKy' : IsCompact {w : Ws | avgPol q g a w = y'} :=
    hcomp {y'} isClosed_singleton (singleton_subset_iff.2 hy'bs)
  have hdeg1 : degree (ZMod q) hWso (avgPol q g a) hAWs y' hKy' = 1 := by
    rw [← degree_congr_open (hA := hAWs) hO inter_subset_left hKy' hKO hfibO]
    refine degree_eq_one_of_straightLine hKO hKO ⟨⟨y', hy'Ws, hy'ar⟩, hAO y' ⟨hy'Ws, hy'ar⟩, rfl⟩
      fun t _ z hz => ?_
    have hz' := hAO z z.2
    rw [hz', ← add_smul, sub_add_cancel, one_smul] at hz
    show avgPol q g a z = y'
    rw [hz', hz]
  -- a non-fixed value `y ∈ B(b, s)`
  obtain ⟨y, ⟨hyV, hyb⟩, hgy⟩ := hacc s hs
  have hKy : IsCompact {w : Ws | avgPol q g a w = y} :=
    hcomp {y} isClosed_singleton (singleton_subset_iff.2 hyb)
  -- degree zero at `y`, on the free part `W* \ Fix g`
  have hgcWs : ContinuousOn g Ws := hgc.mono hWsV
  have hperWs : ∀ w ∈ Ws, g^[q] w = w := fun w hw => hper w (hWsV hw)
  have hW' : IsOpen (Ws \ {z | g z = z}) := isOpen_diff_fixedPoints hWso hgcWs
  have hgW' : MapsTo g (Ws \ {z | g z = z}) (Ws \ {z | g z = z}) :=
    mapsTo_diff_fixedPoints hgWs (hinjg.mono hWsV)
  have hW'Ws : Ws \ {z | g z = z} ⊆ Ws := sdiff_subset
  have hfree : ∀ w ∈ Ws \ {z | g z = z}, g w ≠ w := fun w hw => hw.2
  have hfib' : ∀ w ∈ Ws, avgPol q g a w = y → w ∈ Ws \ {z | g z = z} := by
    intro w hw hAw
    refine ⟨hw, fun hgw => hgy ?_⟩
    have hwy : w = y := (hAfix w hgw).symm.trans hAw
    exact hwy ▸ hgw
  generalize hW'def : Ws \ {z | g z = z} = W' at hW' hgW' hW'Ws hfree hfib'
  have hgcW' : ContinuousOn g W' := hgcWs.mono hW'Ws
  have hperW' : ∀ w ∈ W', g^[q] w = w := fun w hw => hperWs w (hW'Ws hw)
  have hldeg : ∀ j, 0 < j → j < q → ∀ w (hw : w ∈ W'),
      ldeg (ZMod q) hW' (g^[j]) (hgcW'.iterate hgW' j) (injOn_iterate hgW' hperW' j) w hw = 1 := by
    intro j _ _ w hw
    -- `g^[j] = id` near `y'`, so `ldeg_{y'} (g^[j]) = 1` on `W*`
    obtain ⟨τ, hτ, hτO⟩ := Metric.isOpen_iff.1 hO y' ⟨hy'Ws, hy'ar⟩
    have hτ' : closedBall y' (τ / 2) ⊆ Ws ∩ ball a r :=
      (closedBall_subset_ball (by linarith)).trans hτO
    have h1 : ldeg (ZMod q) hWso (g^[j]) (hgcWs.iterate hgWs j) (injOn_iterate hgWs hperWs j) y'
        hy'Ws = 1 :=
      ldeg_eq_one_of_dist_le (by positivity) (hτ'.trans inter_subset_left)
        (fun z hz => by
          rw [iterate_fixed (hfix z (ball_subset_closedBall (hτ' hz).2)) j, dist_self]
          positivity) hy'Ws
    -- (LOC) on the connected `W*`
    have h2 : ldeg (ZMod q) hWso (g^[j]) (hgcWs.iterate hgWs j) (injOn_iterate hgWs hperWs j) w
        (hW'Ws hw) = 1 :=
      (ldeg_eq_of_isPreconnected hWsconn subset_rfl (hW'Ws hw) hy'Ws).trans h1
    rw [← h2]
    -- (D-loc) from `W*` to `W* \ Fix g`
    exact degree_congr_open (hW := hWso) (hA := hgcWs.iterate hgWs j) hW' hW'Ws _ _
      fun z hz hzw => (injOn_iterate hgWs hperWs j hz (hW'Ws hw) hzw) ▸ hw
  have hKW' : IsCompact {w : W' | avgPol q g a w = y} := isCompact_fibre_of_subset hW'Ws hfib' hKy
  have h0 := hT q hW' hgW' hgcW' hperW' hfree hldeg (hAWs.mono hW'Ws)
    (fun w hw => avgPol_apply_eq (hperW' w hw)) hKW'
  have h1 := degree_congr_open (R := ZMod q) (hW := hWso) (hA := hAWs) hW' hW'Ws hKy hKW' hfib'
  rw [hconst y hyb y' hy'bs hKy hKy', hdeg1] at h1
  exact zero_ne_one (h0.symm.trans h1)

end Claims

end HSFormal.Newman
