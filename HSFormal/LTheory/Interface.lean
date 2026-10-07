import HSFormal.LTheory.ConcreteL
import HSFormal.LTheory.Union
import HSFormal.AsymptoticCategory
import Mathlib.Algebra.Exact

/-!
# The hypothesis interface `LowerLTheory` (L-theory module M6)

`LowerLTheory` bundles the ultimate lower L-groups `L = L^{⟨-∞⟩}` of [CP95, Definition 4.16] and
[Ran92, §17] with exactly the published properties used by the manuscript (design §3, H1–H5):
functoriality, unitary invariance and additivity (H4), the decoration maps from the concrete
groups `Lconc` (H3), the localization sequence of every Karoubi filtration with natural boundary
(H1), the pair-boundary formula up to a universal sign (H2), and the Rothenberg isomorphism for
finite-support sums of `Free(ℚ[G])` in degrees `n ≥ 0` (H5).  `BS01` (H6) is a separate `Prop`.

**Non-vacuity (design W7).**  Every field holds for the real `L^{⟨-∞⟩}`; each docstring records
the source and the reason.  Decorations follow the warnings W1–W3: exactness is only asserted for
`L` (never for `Lconc = L^p`), `cls` is a homomorphism `L^p → L^{⟨-∞⟩}` in all degrees, and
bijectivity is only asserted for categories with vanishing negative K-theory and `n ≥ 0`
(for `n < 0`, `Lconc A n = 0` by `Lconc.cls_eq_zero_of_neg`).  H2 carries a sign parameter (W4).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits HSFormal.Compression

noncomputable section

/-! ### `∏ᵢ Free(ℚ[Gᵢ])` and its finite-support subcategories -/

section FreeQG

open AsymptoticObject

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

variable (π : ∀ i, G i →* H) (X : Type) [MulAction H X] [PseudoEMetricSpace X] in
/-- The prequotient asymptotic category (controlled equivariant matrix sequences, no
identifications) with transpose duality; based direct sums are unitary. -/
@[implicit_reducible] def preAsymptoticInvCat : InvCat where
  carrier := AsymptoticObject π X
  inv :=
    { star := transpose
      star_comp := transpose_comp
      star_id _ := transpose_id
      star_add := transpose_add
      star_star := transpose_transpose }
  unitary M N := ⟨{ toBinaryBicone := biprodBicone M N
                    isBilimit := isBinaryBilimitOfTotal _ (biprodBicone_total M N)
                    star_inl := OrbitEmbedding.transpose_incl _
                    star_inr := OrbitEmbedding.transpose_incl _ }⟩

variable (G) in
/-- `∏ᵢ Free(ℚ[Gᵢ])`: based free modules `ℚ[Fin nᵢ × Gᵢ]` with equivariant rational matrices and
transpose duality (the asymptotic prequotient over a point, where control is vacuous). -/
abbrev prodFreeQG : InvCat := preAsymptoticInvCat (fun i ↦ (1 : G i →* Unit)) PUnit

open scoped Classical in
lemma rank_eq_zero_of_id {M : prodFreeQG G} {i : ℕ} (h : (𝟙 M : M ⟶ M).1 i = 0) :
    M.rank i = 0 := by
  by_contra hM
  have : Nonempty (Fin (M.rank i)) := ⟨⟨0, by omega⟩⟩
  exact one_ne_zero (show (1 : Matrix (Fin (M.rank i) × G i) _ ℚ) = 0 from h)

lemma mul_eq_zero_of_rank {α β : Type*} {M : prodFreeQG G} {i : ℕ} (hM : M.rank i = 0)
    (a : Matrix α (Fin (M.rank i) × G i) ℚ) (b : Matrix (Fin (M.rank i) × G i) β ℚ) :
    a * b = 0 := by
  have : IsEmpty (Fin (M.rank i) × G i) := ⟨fun x ↦ by have := x.1.2; omega⟩
  ext; simp [Matrix.mul_apply]

variable (G) in
/-- Objects of `∏ᵢ Free(ℚ[Gᵢ])` of finite support contained in `T`. -/
def finSuppIn (T : Set ℕ) : ObjectProperty (prodFreeQG G) :=
  fun M ↦ {i | M.rank i ≠ 0}.Finite ∧ ∀ i ∉ T, M.rank i = 0

lemma rank_eq_zero_of_iso {M N : prodFreeQG G} (e : M ≅ N) {i : ℕ} (h : M.rank i = 0) :
    N.rank i = 0 :=
  rank_eq_zero_of_id <| by
    rw [← e.inv_hom_id]
    erw [AsymptoticObject.comp_val]
    rw [mul_eq_zero_of_rank h]

instance (T : Set ℕ) : IsAdditiveSub (finSuppIn G T) where
  of_iso e h := ⟨h.1.subset fun i hi h' ↦ hi (rank_eq_zero_of_iso e h'),
    fun i hi ↦ rank_eq_zero_of_iso e (h.2 i hi)⟩
  exists_zero := ⟨zeroObj, isZero_zeroObj, by simp [finSuppIn, zeroObj]⟩
  biprod_mem {M N} b hb hM hN := by
    have key (i : ℕ) (h₁ : M.rank i = 0) (h₂ : N.rank i = 0) : b.pt.rank i = 0 :=
      rank_eq_zero_of_id <| by
        rw [← IsBilimit.binary_total hb]
        erw [AsymptoticObject.add_val, AsymptoticObject.comp_val, AsymptoticObject.comp_val]
        rw [mul_eq_zero_of_rank h₁, mul_eq_zero_of_rank h₂, add_zero]
    refine ⟨(hM.1.union hN.1).subset fun i hi ↦ ?_, fun i hi ↦ key i (hM.2 i hi) (hN.2 i hi)⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hi (key i h.1 h.2)

variable (G) in
/-- `⊕_{i ∈ T} Free(ℚ[Gᵢ])`, the finite-support subcategory of `∏_{i ∈ T} Free(ℚ[Gᵢ])`;
`T = {i}` gives a single `Free(ℚ[Gᵢ])`, `T = univ` the sum of manuscript l. 156–162. -/
abbrev finSuppFreeQG (T : Set ℕ) : InvCat := (prodFreeQG G).sub (finSuppIn G T)

end FreeQG

/-! ### Idempotent splitting [BS01] -/

/-- The complex `C` is concentrated in degrees `[lo, hi]`. -/
def BoundedIn {V : Type*} [Category V] [Preadditive V] (C : ChainComplex V ℤ) (lo hi : ℤ) :
    Prop :=
  ∀ r, r < lo ∨ hi < r → IsZero (C.X r)

/-- **H6** ([BS01, Theorem 2.8] for the split exact structure on `Kar A`, where
`D^b(Kar A) = K^b(Kar A)`): `K^b(Kar A)` is idempotent complete, i.e. a homotopy idempotent `e` of
a bounded complex over `A` splits through a bounded Kar complex `(D, q)`.  Stated on `Kar A`,
never on `A` itself (design W6). -/
def BS01 : Prop :=
  ∀ (A : InvCat) (C : ChainComplex A ℤ) (lo hi : ℤ), BoundedIn C lo hi →
    ∀ e : C ⟶ C, Homotopy (e ≫ e) e →
      ∃ (D : ChainComplex A ℤ) (q : D ⟶ D) (lo' hi' : ℤ) (ι : D ⟶ C) (r : C ⟶ D),
        q ≫ q = q ∧ SupportedIn q lo' hi' ∧ q ≫ ι = ι ∧ r ≫ q = r ∧
          Nonempty (Homotopy (r ≫ ι) e) ∧ Nonempty (Homotopy (ι ≫ r) q)

/-! ### The interface -/

/-- **Ultimate lower L-theory** `L = L^{⟨-∞⟩}` with its published properties (design §3).
The real theory: `L A n = π_n 𝐋^{-∞}(A)` of [CP95, Definition 4.16], identified with Ranicki's
`L^{⟨-∞⟩}_n(A) = colim_j L^{⟨-j⟩}_n(A)` [Ran92, §17]; over `ℚ` quadratic and symmetric
L-groups agree [Ran80I, Prop. 3.3].  Using one `L` for CP95's spectrum and Ranicki's decorations
is design I1. -/
structure LowerLTheory where
  /-- The groups `L^{⟨-∞⟩}_n(A)`, defined for every small additive category with involution and
  every `n ∈ ℤ` ([Ran92, §17]; 4-periodic). -/
  L : InvCat → ℤ → Type
  [grp : ∀ A n, AddCommGroup (L A n)]
  /-- **H4** Functoriality along duality-preserving functors: `L^{⟨-∞⟩}` is a functor on
  additive categories with involution ([Ran92, §17]; [CP95, Definition 4.16]); `InvFunctor`s are
  strict morphisms of such, so this is a restriction. -/
  map : ∀ {A B : InvCat}, (A ⟶ B) → ∀ n, L A n →+ L B n
  map_id : ∀ (A : InvCat) n, map (𝟙 A) n = AddMonoidHom.id _
  map_comp : ∀ {A B C : InvCat} (Φ : A ⟶ B) (Ψ : B ⟶ C) n,
    map (Φ ≫ Ψ) n = (map Ψ n).comp (map Φ n)
  /-- **H4** A unitary natural isomorphism `η : Φ ≅ Ψ` (`η^* = η⁻¹`) induces the same map
  ([Ran89, §§3–6]): `η` is an isomorphism of Poincaré complexes `Φ(C, φ) ≅ Ψ(C, φ)` over every
  bounded category `C_{ℤ^j}(A)` defining `L^{⟨-j⟩}` [Ran92, §17], hence also on the colimit.
  Proved for `Lconc` in `Lconc.map_eq_of_unitaryIso`. -/
  map_unitaryIso : ∀ {A B : InvCat} {Φ Ψ : A ⟶ B}, InvCat.UnitaryIso Φ Ψ → ∀ n, map Φ n = map Ψ n
  /-- **H4** Additivity: if `S` is a finite unitary sum of the `Φᵢ`, then `S(C, φ) ≅ ⊕ᵢ Φᵢ(C, φ)`
  isometrically (on every `C_{ℤ^j}(A)`), so `S_* = ∑ᵢ (Φᵢ)_*` ([Ran89, §§3–6], [Ran92, §17]).
  Proved for `Lconc` in `Lconc.map_finSum`. -/
  map_finSum : ∀ {A B : InvCat} {ι : Type} [Fintype ι] {Φ : ι → (A ⟶ B)} {S : A ⟶ B},
    InvCat.IsFinSum Φ S → ∀ n, map S n = ∑ i, map (Φ i) n
  /-- **H3** The decoration map `L^p_N(A) → L^{⟨-∞⟩}_N(A)` of [Ran92, Theorem 17.2 and
  Definition 17.7] on `Lconc A N`, which is `L^p_N(A) = L_N(Kar A)` for `N ≥ 0` (design §2.1:
  strict structures are exact over `ℚ`; relations hold in `L^p`) and `0` for `N < 0`. -/
  cls : ∀ (A : InvCat) N, Lconc A N →+ L A N
  /-- **H3** Naturality of the decoration maps ([Ran92, Theorem 17.2]). -/
  cls_map : ∀ {A B : InvCat} (Φ : A ⟶ B) N x, cls B N (Lconc.map Φ x) = map Φ N (cls A N x)
  /-- **H1** The boundary `∂ : L_{n+1}(A/U) → L_n(U)` of the localization sequence of
  [CP95, Theorem 4.2] (homotopy fibration `𝐋^{-∞}(U) → 𝐋^{-∞}(A) → 𝐋^{-∞}(A/U)`), for a
  Karoubi filtration in the sense of [CP95, Definition 1.27]; `KaroubiFiltration` implies all of
  its axioms (design W5), and `U` is invariant under the object-fixing involution.  No negative
  K-theory hypothesis is needed for localization (manuscript l. 34). -/
  bdry : ∀ {A : InvCat} (F : KaroubiFiltration A) n, L F.quot (n + 1) →+ L F.sub n
  /-- **H1** Exactness at `L_n(A)` ([CP95, Theorem 4.2], long exact sequence of homotopy groups;
  for `L^{⟨-∞⟩}` only, never for `L^p`, design W1). -/
  exact_A : ∀ {A : InvCat} (F : KaroubiFiltration A) n,
    Function.Exact (map F.incl n) (map F.proj n)
  /-- **H1** Exactness at `L_{n+1}(A/U)` ([CP95, Theorem 4.2]). -/
  exact_Q : ∀ {A : InvCat} (F : KaroubiFiltration A) n,
    Function.Exact (map F.proj (n + 1)) (bdry F n)
  /-- **H1** Exactness at `L_n(U)` ([CP95, Theorem 4.2]). -/
  exact_U : ∀ {A : InvCat} (F : KaroubiFiltration A) n,
    Function.Exact (bdry F n) (map F.incl n)
  /-- **H1** Naturality of `∂` for maps of filtered categories: the fibration of
  [CP95, Theorem 4.2] is functorial in functors `(A, U) → (A', U')` ([CP95, Definition 4.16]),
  so the induced map of long exact sequences commutes with `∂`. -/
  bdry_natural : ∀ {A B : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
    (Φ : FiltrationHom F F') n,
    (bdry F' n).comp (map Φ.quot (n + 1)) = (map Φ.sub n).comp (bdry F n)
  /-- **H2** The universal sign relating `∂` to boundaries of pairs in our cone/dual conventions
  (design W4, I2). -/
  bsign : ℤ → ℤˣ
  /-- **H2** An `(N+1)`-dimensional Poincaré pair over `A` whose boundary lies in `U` represents
  a closed complex over `A/U` (`SymPair.toQuot`, M3), and `∂` sends its class to the class of the
  boundary lifted to `U` (`SymPair.bdLift`), up to the universal sign `bsign N`
  ([CP95, proof of Theorem 4.1]; manuscript Lemma 4.1, l. 217–237). -/
  bdry_pair : ∀ {A : InvCat} (F : KaroubiFiltration A) {N : ℤ} (X : SymPair A.inv N)
    (hU : ∀ r, F.U (X.bd.C.X r)),
    bdry F N (cls F.quot (N + 1) (Lconc.cls (X.toQuot F hU))) =
      bsign N • cls F.sub N (Lconc.cls (X.bdLift F hU))
  /-- **H5** For `⊕_{i ∈ T} Free(ℚ[Gᵢ])` with `Gᵢ` finite and `n ≥ 0`, the decoration map
  `L^p_n → L^{⟨-∞⟩}_n` is bijective: by the Rothenberg sequences [Ran92, Theorem 17.2] it
  suffices that `K_{-k} = 0` for `k ≥ 1`, which holds for each semisimple `ℚ[Gᵢ]`
  [Wei13, III.4.1] with `K_{-k}(Free R) = K_{-k}(R)` [Ran92, §11, p. 101], and for the
  finite-support sum by the finite-block argument (manuscript l. 156–162).  Restricted to these
  categories (design W2) and to `n ≥ 0`, where `Lconc = L^p` (audit addendum). -/
  dec_bij : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (n : ℤ),
    0 ≤ n → Function.Bijective (cls (finSuppFreeQG G T) n)

attribute [instance] LowerLTheory.grp

namespace LowerLTheory

variable (𝕃 : LowerLTheory) {A B : InvCat}

/-- A unitary equivalence of `InvCat`s induces an isomorphism of L-groups. -/
def mapAddEquiv (Φ : A ⟶ B) (Ψ : B ⟶ A) (h₁ : InvCat.UnitaryIso (Φ ≫ Ψ) (𝟙 A))
    (h₂ : InvCat.UnitaryIso (Ψ ≫ Φ) (𝟙 B)) (n : ℤ) : 𝕃.L A n ≃+ 𝕃.L B n :=
  AddEquiv.ofBijective (𝕃.map Φ n) <| Function.bijective_iff_has_inverse.mpr
    ⟨𝕃.map Ψ n,
      fun x ↦ by rw [← AddMonoidHom.comp_apply, ← 𝕃.map_comp, 𝕃.map_unitaryIso h₁, 𝕃.map_id]; rfl,
      fun x ↦ by rw [← AddMonoidHom.comp_apply, ← 𝕃.map_comp, 𝕃.map_unitaryIso h₂, 𝕃.map_id]; rfl⟩

lemma proj_comp_incl (F : KaroubiFiltration A) (n : ℤ) (x : 𝕃.L F.sub n) :
    𝕃.map F.proj n (𝕃.map F.incl n x) = 0 :=
  (𝕃.exact_A F n _).mpr ⟨x, rfl⟩

lemma bdry_proj (F : KaroubiFiltration A) (n : ℤ) (x : 𝕃.L A (n + 1)) :
    𝕃.bdry F n (𝕃.map F.proj (n + 1) x) = 0 :=
  (𝕃.exact_Q F n _).mpr ⟨x, rfl⟩

lemma incl_bdry (F : KaroubiFiltration A) (n : ℤ) (x : 𝕃.L F.quot (n + 1)) :
    𝕃.map F.incl n (𝕃.bdry F n x) = 0 :=
  (𝕃.exact_U F n _).mpr ⟨x, rfl⟩

end LowerLTheory

namespace Lconc

variable {A B : InvCat} {N : ℤ}

/-- A unitary equivalence of `InvCat`s induces an isomorphism of concrete L-groups. -/
def mapAddEquiv (Φ : A ⟶ B) (Ψ : B ⟶ A) (h₁ : InvCat.UnitaryIso (Φ ≫ Ψ) (𝟙 A))
    (h₂ : InvCat.UnitaryIso (Ψ ≫ Φ) (𝟙 B)) : Lconc A N ≃+ Lconc B N :=
  AddEquiv.ofBijective (map Φ) <| Function.bijective_iff_has_inverse.mpr
    ⟨map Ψ,
      fun x ↦ by rw [← AddMonoidHom.comp_apply, ← map_comp, map_eq_of_unitaryIso h₁, map_id]; rfl,
      fun x ↦ by rw [← AddMonoidHom.comp_apply, ← map_comp, map_eq_of_unitaryIso h₂, map_id]; rfl⟩

end Lconc

end

end HSFormal.LTheory
