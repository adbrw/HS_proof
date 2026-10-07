import Mathlib

/-!
# [Tao11, Lemma 7], part 2: a copy of `ℤ_p` from separating circle characters

Let `B` be a compact Hausdorff second-countable commutative group whose continuous characters
`B →* Circle` separate points, nontrivial and torsion-free. Then some `ℤ_[p]` embeds
(`HSFormal.Lemma7.exists_padic_embedding_of_chars`).

This is the tower argument of [Tao11, Lemma 7] with the tower given by one character at a time,
so that no Lie theory and no Pontryagin duality is needed; the only structure theory used is that a
closed subgroup of the circle is either the whole circle or of finite exponent
(`HSFormal.Lemma7.closed_subgroup_circle`, from `AddSubgroup.dense_or_cyclic` on `ℝ`).

1. Lindelöf: countably many characters `χ 0, χ 1, …` already separate points, and `χ 0 ≠ 1`.
2. `χ 0 (B)` is a nontrivial closed subgroup of the circle, so it contains an element of prime
   order `p`; pick `b₀` mapping to it.
3. Lifting (`lift_step`): if `χ i b` is a `p`-power root of unity for `i < n`, then `b` can be
   multiplied by an element of `⋂_{i<n} ker χ i` so that `χ n b` becomes a `p`-power root of unity
   too. (The image `S` of that kernel under `χ n` is closed; if `S` is the circle use it, if
   `S ⊆ μ_m` split off the prime-to-`p` part by Bézout.)
4. A cluster point `x` of the resulting sequence has every `χ i x` a `p`-power root of unity and
   `χ 0 x ≠ 1`. Hence the closed subgroups `H k = cl ⟨x^{p^k}⟩` decrease to `{1}`, and by
   compactness eventually lie in any neighbourhood of `1`.
5. `ι a` is the unique point of `⋂ₖ x^{a mod p^k} H k`; it is a continuous homomorphism
   `ℤ_[p] → B` with `ι 1 = x`, injective because a nonzero kernel would contain some `p^v`,
   making `x` a torsion element.
-/

open Topology Filter

namespace HSFormal.Lemma7

/-! ### Closed subgroups of the circle -/

/-- A closed subgroup of the circle is the whole circle or has finite exponent. -/
theorem closed_subgroup_circle (S : Subgroup Circle) (hS : IsClosed (S : Set Circle)) :
    S = ⊤ ∨ ∃ m : ℕ, 0 < m ∧ ∀ s ∈ S, s ^ m = 1 := by
  let T : AddSubgroup ℝ :=
    { carrier := {t | Circle.exp t ∈ S}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Circle.exp_add] at ha hb ⊢
        exact S.mul_mem ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Circle.exp_neg] at ha ⊢
        exact S.inv_mem ha }
  have hTc : IsClosed (T : Set ℝ) := hS.preimage Circle.exp.continuous
  rcases T.dense_or_cyclic with hd | ⟨a, ha⟩
  · left
    have hT : (T : Set ℝ) = Set.univ := by rw [← hTc.closure_eq]; exact hd.closure_eq
    rw [eq_top_iff]
    intro s _
    obtain ⟨t, rfl⟩ := Circle.exp_surjective s
    have : t ∈ (T : Set ℝ) := by rw [hT]; trivial
    exact this
  · right
    have h2pi : 2 * Real.pi ∈ T := by
      show Circle.exp (2 * Real.pi) ∈ S
      simp
    rw [ha, AddSubgroup.mem_closure_singleton] at h2pi
    obtain ⟨k, hk⟩ := h2pi
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk
      linarith [Real.pi_pos]
    refine ⟨k.natAbs, Int.natAbs_pos.2 hk0, fun s hs => ?_⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective s
    have ht : t ∈ T := hs
    rw [ha, AddSubgroup.mem_closure_singleton] at ht
    obtain ⟨j, rfl⟩ := ht
    have hpow : Circle.exp (j • a) ^ k = 1 := by
      rw [← Circle.exp_zsmul, smul_smul, mul_comm, ← smul_smul, hk, zsmul_eq_mul]
      exact Circle.exp_int_mul_two_pi j
    rcases Int.natAbs_eq k with h | h
    · rw [h, zpow_natCast] at hpow
      exact hpow
    · rw [h, zpow_neg, inv_eq_one, zpow_natCast] at hpow
      exact hpow

/-- Splitting off the prime-to-`p` part inside a closed subgroup of the circle. -/
theorem circle_ppart (S : Subgroup Circle) (hS : IsClosed (S : Set Circle)) {p : ℕ}
    (hp : p.Prime) (k : ℕ) (z : Circle) (hz : z ^ p ^ k ∈ S) :
    ∃ w ∈ S, ∃ j : ℕ, (z * w⁻¹) ^ p ^ j = 1 := by
  rcases closed_subgroup_circle S hS with rfl | ⟨m, hm, hmS⟩
  · exact ⟨z, Subgroup.mem_top z, 0, by simp⟩
  · obtain ⟨a, m', hpm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.one_lt.ne'
    have hcop : Nat.Coprime (p ^ (k + a)) m' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm')
    have hb := Nat.gcd_eq_gcd_ab (p ^ (k + a)) m'
    rw [hcop.gcd_eq_one] at hb
    set u := Nat.gcdA (p ^ (k + a)) m'
    set v := Nat.gcdB (p ^ (k + a)) m'
    have h1 : (z ^ p ^ k) ^ (p ^ a * m') = 1 := hmS _ hz
    refine ⟨(z ^ p ^ k) ^ (u * ((p ^ a : ℕ) : ℤ)), S.zpow_mem hz _, k + a, ?_⟩
    have hzw : z * ((z ^ p ^ k) ^ (u * ((p ^ a : ℕ) : ℤ)))⁻¹ = z ^ (v * (m' : ℤ)) := by
      rw [← zpow_natCast z (p ^ k), ← zpow_mul, ← zpow_neg, ← zpow_one_add]
      congr 1
      push_cast at hb ⊢
      rw [pow_add] at hb
      linear_combination hb
    rw [hzw, ← zpow_natCast, ← zpow_mul]
    have hexp : v * (m' : ℤ) * ((p ^ (k + a) : ℕ) : ℤ) =
        ((p ^ k : ℕ) : ℤ) * ((p ^ a * m' : ℕ) : ℤ) * v := by
      push_cast
      ring
    rw [hexp, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow]

/-! ### The tower argument -/

variable {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B]
  [T2Space B]

omit [IsTopologicalGroup B] [T2Space B] in
/-- The lifting step of the tower: the first `n` characters can be kept fixed while the `n`-th
becomes a `p`-power root of unity. -/
theorem lift_step (χ : ℕ → B →* Circle) (hχ : ∀ n, Continuous (χ n)) {p : ℕ} (hp : p.Prime)
    (n : ℕ) (b : B) (hb : ∀ i < n, ∃ k, χ i b ^ p ^ k = 1) :
    ∃ b' : B, (∀ i < n, χ i b' = χ i b) ∧ ∃ k, χ n b' ^ p ^ k = 1 := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ i < n, χ i b ^ p ^ K = 1 := by
    choose! kf hkf using hb
    refine ⟨∑ i ∈ Finset.range n, kf i, fun i hi => ?_⟩
    have hle : kf i ≤ ∑ j ∈ Finset.range n, kf j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, pow_mul, hkf i hi, one_pow]
  let Kn : Subgroup B :=
    { carrier := {c | ∀ i < n, χ i c = 1}
      mul_mem' := fun {c d} hc hd i hi => by
        rw [map_mul, hc i hi, hd i hi, one_mul]
      one_mem' := fun i _ => map_one _
      inv_mem' := fun {c} hc i hi => by
        rw [map_inv, hc i hi, inv_one] }
  have hKc : IsClosed (Kn : Set B) := by
    show IsClosed {c : B | ∀ i < n, χ i c = 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hχ i) continuous_const
  let S : Subgroup Circle := Kn.map (χ n)
  have hSc : IsClosed (S : Set Circle) := by
    rw [Subgroup.coe_map]
    exact (hKc.isCompact.image (hχ n)).isClosed
  have hz : χ n b ^ p ^ K ∈ S :=
    ⟨b ^ p ^ K, fun i hi => by rw [map_pow, hK i hi], by rw [map_pow]⟩
  obtain ⟨w, ⟨c, hc, rfl⟩, j, hj⟩ := circle_ppart S hSc hp K (χ n b) hz
  refine ⟨b * c⁻¹, fun i hi => ?_, j, ?_⟩
  · have hci : χ i c = 1 := hc i hi
    rw [map_mul, map_inv, hci, inv_one, mul_one]
  · rw [map_mul, map_inv]
    exact hj

omit [IsTopologicalGroup B] [T2Space B] in
/-- The base of the tower: a nontrivial continuous character takes a value of prime order. -/
theorem exists_base (χ0 : B →* Circle) (hχ0 : Continuous χ0) (hne : χ0 ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ∃ b : B, χ0 b ≠ 1 ∧ χ0 b ^ p = 1 := by
  have hSc : IsClosed (χ0.range : Set Circle) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range hχ0).isClosed
  rcases closed_subgroup_circle χ0.range hSc with hS | ⟨m, hm, hmS⟩
  · have hmem : Circle.exp Real.pi ∈ χ0.range := hS ▸ Subgroup.mem_top _
    obtain ⟨b, hb⟩ := hmem
    refine ⟨2, Nat.prime_two, b, ?_, ?_⟩
    · rw [hb]
      intro h
      rw [Circle.exp_eq_one] at h
      obtain ⟨n, hn⟩ := h
      have h1 : (1 : ℝ) = 2 * n := by
        have hpi := Real.pi_pos
        have : Real.pi * 1 = Real.pi * (2 * n) := by linarith
        exact mul_left_cancel₀ hpi.ne' this
      have h2 : (1 : ℤ) = 2 * n := by exact_mod_cast h1
      omega
    · rw [hb, ← Circle.exp_nsmul]
      have : (2 : ℕ) • Real.pi = 2 * Real.pi := by rw [nsmul_eq_mul]; norm_num
      rw [this, Circle.exp_two_pi]
  · obtain ⟨b0, hb0⟩ : ∃ b, χ0 b ≠ 1 := by
      by_contra h
      push Not at h
      exact hne (MonoidHom.ext h)
    set s := χ0 b0 with hsdef
    have hs : s ^ m = 1 := hmS s ⟨b0, rfl⟩
    have hord : orderOf s ≠ 0 :=
      (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hs⟩)).ne'
    have hord1 : orderOf s ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
    refine ⟨p, hp, b0 ^ (orderOf s / p), ?_, ?_⟩
    · rw [map_pow]
      intro h
      have := orderOf_pow_orderOf_div hord hpd
      rw [← hsdef] at h
      rw [h, orderOf_one] at this
      exact hp.one_lt.ne this
    · rw [map_pow, ← hsdef, ← pow_mul, Nat.div_mul_cancel hpd, pow_orderOf_eq_one]

omit [IsTopologicalGroup B] [T2Space B] in
/-- The limit of the tower: a point all of whose character values are `p`-power roots of unity,
with prescribed value under `χ 0`. -/
theorem exists_padic_point [FirstCountableTopology B] (χ : ℕ → B →* Circle)
    (hχ : ∀ n, Continuous (χ n)) {p : ℕ} (hp : p.Prime) (b0 : B)
    (hb0 : ∃ k, χ 0 b0 ^ p ^ k = 1) :
    ∃ x : B, χ 0 x = χ 0 b0 ∧ ∀ i, ∃ k, χ i x ^ p ^ k = 1 := by
  have step : ∀ n : ℕ, ∀ b : B, (∀ i < n + 1, ∃ k, χ i b ^ p ^ k = 1) →
      ∃ b' : B, (∀ i < n + 1, χ i b' = χ i b) ∧ ∀ i < n + 2, ∃ k, χ i b' ^ p ^ k = 1 := by
    intro n b hb
    obtain ⟨b', h1, k, h2⟩ := lift_step χ hχ hp (n + 1) b hb
    refine ⟨b', h1, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [h1 i hi]
      exact hb i hi
    · exact ⟨k, h2⟩
  choose! nxt hnxt1 hnxt2 using step
  let seq : ℕ → B := fun n => Nat.rec (motive := fun _ => B) b0 (fun n b => nxt n b) n
  have hseqs : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have hgood : ∀ n, ∀ i < n + 1, ∃ k, χ i (seq n) ^ p ^ k = 1 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact hb0
    | succ n ih =>
      rw [hseqs]
      exact hnxt2 n (seq n) ih
  have hstab : ∀ i n, i ≤ n → χ i (seq n) = χ i (seq i) := by
    intro i n hin
    induction n, hin using Nat.le_induction with
    | base => rfl
    | succ n hin ih => rw [hseqs, hnxt1 n (seq n) (hgood n) i (by omega), ih]
  obtain ⟨x, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq seq
  have hval : ∀ i, χ i x = χ i (seq i) := by
    intro i
    have h1 : Tendsto (fun m => χ i (seq (φ m))) atTop (𝓝 (χ i x)) :=
      ((hχ i).tendsto x).comp hlim
    have h2 : Tendsto (fun m => χ i (seq (φ m))) atTop (𝓝 (χ i (seq i))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop i] with m hm
      exact (hstab i (φ m) (le_trans hm (hφ.id_le m))).symm
    exact tendsto_nhds_unique h1 h2
  refine ⟨x, hval 0, fun i => ?_⟩
  rw [hval i]
  exact hgood i i (Nat.lt_succ_self i)

/-! ### The pro-`p` filtration `H k = cl ⟨x^{p^k}⟩` -/

/-- `H x p k` is the closed subgroup generated by `x ^ p ^ k`. -/
def H (x : B) (p k : ℕ) : Subgroup B := (Subgroup.zpowers (x ^ p ^ k)).topologicalClosure

omit [CompactSpace B] [T2Space B] in
theorem H_antitone (x : B) (p : ℕ) : Antitone (H x p) := by
  apply antitone_nat_of_succ_le
  intro k
  apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_topologicalClosure _)
  rw [Subgroup.zpowers_le]
  apply Subgroup.le_topologicalClosure
  rw [pow_succ, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit [CompactSpace B] [T2Space B] in
theorem iInter_H_eq_one (χ : ℕ → B →* Circle) (hχ : ∀ n, Continuous (χ n))
    (hsep : ∀ b : B, b ≠ 1 → ∃ n, χ n b ≠ 1) {p : ℕ} {x : B}
    (hx : ∀ i, ∃ k, χ i x ^ p ^ k = 1) (y : B) (hy : ∀ k, y ∈ H x p k) : y = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hsep y hne
  obtain ⟨k, hk⟩ := hx i
  apply hi
  have hker : H x p k ≤ (χ i).ker := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, map_pow]
      exact hk
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (hχ i)
  exact hker (hy k)

theorem H_shrink {p : ℕ} {x : B} (hint : ∀ y : B, (∀ k, y ∈ H x p k) → y = 1) :
    ∀ U ∈ 𝓝 (1 : B), ∃ k, (H x p k : Set B) ⊆ U := by
  intro U hU
  have hdir : Directed (· ⊇ ·) (fun k => (H x p k : Set B)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact H_antitone x p (le_max_left i j)
    · exact H_antitone x p (le_max_right i j)
  have hcpt : ∀ k, IsCompact (H x p k : Set B) :=
    fun k => (Subgroup.isClosed_topologicalClosure _).isCompact
  have hI : (⋂ k, (H x p k : Set B)) = {1} := by
    ext y
    simp only [Set.mem_iInter, SetLike.mem_coe, Set.mem_singleton_iff]
    exact ⟨hint y, fun hy k => hy ▸ (H x p k).one_mem⟩
  have hU' : U ∈ 𝓝ˢ (⋂ k, (H x p k : Set B)) := by
    rw [hI, nhdsSet_singleton]
    exact hU
  exact exists_subset_nhds_of_isCompact hdir hcpt hU'

/-! ### The continuous homomorphism `ℤ_[p] → B` -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The truncated exponent `a mod p^k ∈ [0, p^k)`. -/
noncomputable def ex (k : ℕ) (a : ℤ_[p]) : ℕ := (PadicInt.toZModPow k a).val

theorem ex_cast (k : ℕ) (a : ℤ_[p]) : ((ex k a : ℕ) : ZMod (p ^ k)) = PadicInt.toZModPow k a := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact ZMod.natCast_zmod_val _

theorem ex_succ (k : ℕ) (a : ℤ_[p]) :
    ((ex (k + 1) a : ℕ) : ZMod (p ^ k)) = ((ex k a : ℕ) : ZMod (p ^ k)) := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ex_cast, ex, ZMod.natCast_val, PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k)]

theorem ex_add (k : ℕ) (a b : ℤ_[p]) :
    ((ex k (a + b) : ℕ) : ZMod (p ^ k)) = ((ex k a + ex k b : ℕ) : ZMod (p ^ k)) := by
  rw [Nat.cast_add, ex_cast, ex_cast, ex_cast, map_add]

theorem ex_one (k : ℕ) : ((ex k (1 : ℤ_[p]) : ℕ) : ZMod (p ^ k)) = ((1 : ℕ) : ZMod (p ^ k)) := by
  rw [ex_cast, map_one, Nat.cast_one]

variable (x : B)

omit [CompactSpace B] [T2Space B] hp in
/-- In `B ⧸ H k`, the image of `x` has order dividing `p ^ k`, so its powers only depend on the
exponent mod `p ^ k`. -/
theorem qpow_congr (k m m' : ℕ) (h : (m : ZMod (p ^ k)) = (m' : ZMod (p ^ k))) :
    ((x : B ⧸ H x p k)) ^ m = ((x : B ⧸ H x p k)) ^ m' := by
  have h1 : ((x : B ⧸ H x p k)) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  rw [pow_eq_pow_mod m h1, pow_eq_pow_mod m' h1, (ZMod.natCast_eq_natCast_iff' m m' (p ^ k)).1 h]

/-- The `k`-th approximation set for `ι a`: the coset `x ^ (a mod p^k) * H k`. -/
def D (k : ℕ) (a : ℤ_[p]) : Set B := {y | (y : B ⧸ H x p k) = (x : B ⧸ H x p k) ^ ex k a}

omit [CompactSpace B] [T2Space B] in
theorem mem_D_iff (k : ℕ) (a : ℤ_[p]) (y : B) : y ∈ D x k a ↔ y⁻¹ * x ^ ex k a ∈ H x p k := by
  rw [D, Set.mem_ofPred_eq, ← QuotientGroup.mk_pow, QuotientGroup.eq]

omit [CompactSpace B] [T2Space B] in
theorem isClosed_D (k : ℕ) (a : ℤ_[p]) : IsClosed (D x k a) := by
  have : D x k a = (fun y : B => y⁻¹ * x ^ ex k a) ⁻¹' (H x p k : Set B) := by
    ext y
    rw [mem_D_iff]
    rfl
  rw [this]
  exact (Subgroup.isClosed_topologicalClosure _).preimage (continuous_inv.mul continuous_const)

omit [CompactSpace B] [T2Space B] in
theorem D_succ_subset (k : ℕ) (a : ℤ_[p]) : D x (k + 1) a ⊆ D x k a := by
  intro y hy
  rw [mem_D_iff] at hy
  have hy' : y⁻¹ * x ^ ex (k + 1) a ∈ H x p k := H_antitone x p (Nat.le_succ k) hy
  simp only [D, Set.mem_ofPred_eq]
  rw [← qpow_congr x k _ _ (ex_succ k a), ← QuotientGroup.mk_pow, QuotientGroup.eq]
  exact hy'

omit [T2Space B] in
theorem nonempty_iInter_D (a : ℤ_[p]) : (⋂ k, D x k a).Nonempty := by
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun k => D_succ_subset x k a) (fun k => ⟨x ^ ex k a, ?_⟩) (isClosed_D x 0 a).isCompact
    (fun k => isClosed_D x k a)
  simp [D, QuotientGroup.mk_pow]

omit [CompactSpace B] [T2Space B] in
theorem eq_of_mem_D (hint : ∀ y : B, (∀ k, y ∈ H x p k) → y = 1) (a : ℤ_[p]) (y y' : B)
    (hy : ∀ k, y ∈ D x k a) (hy' : ∀ k, y' ∈ D x k a) : y = y' := by
  have : y⁻¹ * y' = 1 := by
    apply hint
    intro k
    have h1 := hy k
    have h2 := hy' k
    simp only [D, Set.mem_ofPred_eq] at h1 h2
    rw [← QuotientGroup.eq, h1, h2]
  rw [inv_mul_eq_one] at this
  exact this

/-- **The continuous homomorphism `ℤ_[p] → B` with `1 ↦ x`**, for `x` whose `p`-power filtration
shrinks to `1`. -/
theorem exists_padic_hom (hint : ∀ y : B, (∀ k, y ∈ H x p k) → y = 1) :
    ∃ ι : Multiplicative ℤ_[p] →* B, Continuous ι ∧ ι (Multiplicative.ofAdd 1) = x := by
  have hex : ∀ a : ℤ_[p], ∃ y : B, ∀ k, y ∈ D x k a := by
    intro a
    obtain ⟨y, hy⟩ := nonempty_iInter_D x a
    exact ⟨y, Set.mem_iInter.1 hy⟩
  choose f hf using hex
  have huniq : ∀ a y, (∀ k, y ∈ D x k a) → y = f a :=
    fun a y hy => eq_of_mem_D x hint a y (f a) hy (hf a)
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    symm
    apply huniq
    intro k
    have h1 := hf a k
    have h2 := hf b k
    simp only [D, Set.mem_ofPred_eq] at h1 h2 ⊢
    rw [QuotientGroup.mk_mul, h1, h2, ← pow_add, qpow_congr x k _ _ (ex_add k a b)]
  let ι : Multiplicative ℤ_[p] →* B :=
    MonoidHom.mk' (fun a => f (Multiplicative.toAdd a)) (fun a b => hadd _ _)
  have hι1 : ι (Multiplicative.ofAdd 1) = x := by
    symm
    apply huniq
    intro k
    simp only [D, Set.mem_ofPred_eq, toAdd_ofAdd]
    rw [qpow_congr x k _ _ (ex_one k), pow_one]
  refine ⟨ι, ?_, hι1⟩
  apply continuous_of_continuousAt_one
  have h0 : ι 1 = 1 := map_one ι
  rw [ContinuousAt, h0]
  intro U hU
  obtain ⟨k, hk⟩ := H_shrink hint U hU
  have hr : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(k : ℤ))) ∈ 𝓝 (0 : ℤ_[p]) :=
    Metric.closedBall_mem_nhds _ hr
  have hpre : (fun a : ℤ_[p] => f a) ⁻¹' U ∈ 𝓝 (0 : ℤ_[p]) := by
    filter_upwards [hball] with a ha
    rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker] at ha
    have hfa := hf a k
    have hexa : ex k a = 0 := by
      simp only [ex]
      rw [ha, ZMod.val_zero]
    simp only [D, Set.mem_ofPred_eq, hexa, pow_zero, QuotientGroup.eq_one_iff] at hfa
    exact hk hfa
  exact hpre

omit [IsTopologicalGroup B] [CompactSpace B] in
/-- The homomorphism is injective as soon as `x` is not a torsion element. -/
theorem padic_hom_injective (ι : Multiplicative ℤ_[p] →* B) (hc : Continuous ι)
    (hι1 : ι (Multiplicative.ofAdd 1) = x) (hx : ¬ IsOfFinOrder x) : Function.Injective ι := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  set l : ℤ_[p] := Multiplicative.toAdd a with hl
  have hl0 : l ≠ 0 := by
    intro h
    apply hne
    rw [← ofAdd_toAdd a, ← hl, h, ofAdd_zero]
  have hnat : ∀ n : ℕ, ι (Multiplicative.ofAdd ((n : ℤ_[p]) * l)) = 1 := by
    intro n
    rw [← nsmul_eq_mul, ofAdd_nsmul, map_pow, hl, ofAdd_toAdd, ha, one_pow]
  have hall : ∀ c : ℤ_[p], ι (Multiplicative.ofAdd (c * l)) = 1 := by
    have hcl : IsClosed {c : ℤ_[p] | ι (Multiplicative.ofAdd (c * l)) = 1} := by
      apply isClosed_eq _ continuous_const
      exact hc.comp (continuous_ofAdd.comp (continuous_id.mul continuous_const))
    have hsub : Set.range (Nat.cast : ℕ → ℤ_[p]) ⊆
        {c : ℤ_[p] | ι (Multiplicative.ofAdd (c * l)) = 1} := by
      rintro _ ⟨n, rfl⟩
      exact hnat n
    intro c
    exact hcl.closure_subset_iff.mpr hsub (PadicInt.denseRange_natCast c)
  have hspec := PadicInt.unitCoeff_spec hl0
  set u := PadicInt.unitCoeff hl0
  have hpv : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * l = (p : ℤ_[p]) ^ l.valuation := by
    conv_lhs => rw [hspec]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  have h1 := hall ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  rw [hpv] at h1
  have h2 : ι (Multiplicative.ofAdd ((p : ℤ_[p]) ^ l.valuation)) = x ^ (p ^ l.valuation) := by
    rw [← hι1, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, Nat.cast_pow]
  rw [h2] at h1
  exact hx (isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ l.valuation, pow_pos hp.out.pos _, h1⟩)

end Padic

/-! ### Assembly -/

omit [IsTopologicalGroup B] [CompactSpace B] [T2Space B] in
/-- Lindelöf: countably many continuous characters already separate points. -/
theorem exists_countable_sep [SecondCountableTopology B]
    (hsep : ∀ b : B, b ≠ 1 → ∃ χ : B →* Circle, Continuous χ ∧ χ b ≠ 1) :
    ∃ χ : ℕ → B →* Circle, (∀ n, Continuous (χ n)) ∧ ∀ b, b ≠ 1 → ∃ n, χ n b ≠ 1 := by
  let s : {χ : B →* Circle // Continuous χ} → Set B := fun χ => {b | χ.1 b ≠ 1}
  have hs : ∀ i, IsOpen (s i) := fun χ => isOpen_ne_fun χ.2 continuous_const
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable s hs
  let one : {χ : B →* Circle // Continuous χ} := ⟨1, continuous_const⟩
  obtain ⟨f, hf⟩ := (hTc.insert one).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨fun n => (f n).1, fun n => (f n).2, fun b hb => ?_⟩
  have hbU : b ∈ ⋃ i, s i := by
    obtain ⟨χ, hχc, hχb⟩ := hsep b hb
    exact Set.mem_iUnion.2 ⟨⟨χ, hχc⟩, hχb⟩
  rw [← hTU] at hbU
  simp only [Set.mem_iUnion] at hbU
  obtain ⟨i, hiT, hbi⟩ := hbU
  have hi : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem _ hiT
  obtain ⟨n, rfl⟩ := hi
  exact ⟨n, hbi⟩

/-- **[Tao11, Lemma 7] for groups with enough circle characters.** A nontrivial torsion-free
compact Hausdorff second-countable commutative group whose continuous circle characters separate
points contains a continuously embedded copy of some `ℤ_[p]`. -/
theorem exists_padic_embedding_of_chars [SecondCountableTopology B] [Nontrivial B]
    (htf : ∀ g : B, IsOfFinOrder g → g = 1)
    (hsep : ∀ b : B, b ≠ 1 → ∃ χ : B →* Circle, Continuous χ ∧ χ b ≠ 1) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ι : Multiplicative ℤ_[p] →* B),
      Continuous ι ∧ Function.Injective ι := by
  obtain ⟨χ', hχ'c, hχ'sep⟩ := exists_countable_sep hsep
  obtain ⟨g, hg⟩ := exists_ne (1 : B)
  obtain ⟨n0, hn0⟩ := hχ'sep g hg
  let χ : ℕ → B →* Circle := fun i => Nat.casesOn i (χ' n0) χ'
  have hχc : ∀ i, Continuous (χ i) := by
    intro i
    cases i with
    | zero => exact hχ'c n0
    | succ i => exact hχ'c i
  have hχsep : ∀ b : B, b ≠ 1 → ∃ n, χ n b ≠ 1 := by
    intro b hb
    obtain ⟨n, hn⟩ := hχ'sep b hb
    exact ⟨n + 1, hn⟩
  have hχ0 : χ 0 ≠ 1 := by
    intro h
    apply hn0
    show χ 0 g = 1
    rw [h, MonoidHom.one_apply]
  obtain ⟨p, hp, b0, hb0ne, hb0p⟩ := exists_base (χ 0) (hχc 0) hχ0
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx0, hxp⟩ := exists_padic_point χ hχc hp b0 ⟨1, by rw [pow_one]; exact hb0p⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx0
    exact hb0ne hx0.symm
  have hint := iInter_H_eq_one χ hχc hχsep hxp
  obtain ⟨ι, hc, hι1⟩ := exists_padic_hom x hint
  exact ⟨p, ⟨hp⟩, ι, hc, padic_hom_injective x ι hc hι1 fun h => hx1 (htf x h)⟩

end HSFormal.Lemma7
