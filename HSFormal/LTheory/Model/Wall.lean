import HSFormal.LTheory.ConcreteL
import HSFormal.LTheory.Model.BoundaryConstruction
import HSFormal.LTheory.Model.NegK
import HSFormal.LTheory.Model.Transport

/-!
# The symmetric Wall trick under `NegK` (lower L-theory model, module 21)

`blueprint/lower-L-construction.md` §3.2 "H5 from NegK", §4 row 21; `blueprint/negK.md` §1.

Under `NegK B` (in fact under the weaker `NegKStablyFree B`), every strictly symmetric Poincaré
complex `P` over `Kar (C_ℤ^{∘k} B)`, `k ≥ 1`, has the same `Lconc` class as a **free** one: a
complex whose Kar idempotent is `1` in every degree of `[0, N]` (the convention of
`LiftComplex.exists_quotPoincare`).

* `Wall.KarIso e e'`: a Kar isomorphism `(X, e) ≅ (Y, e')`; `refl`, `trans`, `congr`, `zero`,
  `sum` (along arbitrary bicones), `ofStablyFree`, `absorb` (`(M, e) ⊕ F` free if
  `(M, e) ⊕ F ≅ F'`), `absorbSum` (the same for `(M, e) ⊕ (F ⊕ F'')`).
* `Wall.elemComplex F s`: `F` in every degree with `d_{s, s-1} = 1`; `elemIdem` cuts it to the
  elementary contractible Kar complex `F → F` in degrees `(s, s-1)`, contracted by `elemHomotopy`.
  `Wall.ofNullHomotopic`: `(C, p, 0)` with `p ≃ 0` is Poincaré.
* `Wall.isometric_sum_of_φ_eq_zero`: `P ≃ P ⊕ E` whenever `E.φ = 0` (then `E.p ≃ 0`).
* `Wall.strictTransport`: the strict transport of `P` along degreewise Kar isomorphisms
  `(C_r, p_r) ≅ (X_r, q_r)` (chain level: `transportComplex`, `transportHom`, `transportInv`);
  `strictTransportIsometry`.
* `Wall.exists_isometric_free` (`1 ≤ N`): `P` is homotopy isometric to a free complex
  (add the elementary pieces on `F_r` in degrees `(r, r-1)`, resp. `(1, 0)` for `r = 0`).
* `Wall.exists_cls_free_dim_zero` (`N = 0`): no elementary piece fits in `[0, 0]`; instead add the
  algebraic boundary `∂(F[1], 0)` (`SymComplex.boundary`, hyperbolic on `F ⊕ F`), which is
  null-cobordant (`nullCobordant_boundary`).  Here `P` is in general **not** isometric to a free
  complex (its degree-0 object is only stably free).
* **Relative version** (Kar complexes and pairs, via `Transport.lean`): `karHtpyEquivSumElem`
  (`(D, p) ≃ (D ⊕ E, p ⊕ e)`), `transportKarHtpyEquiv`, `exists_karHtpyEquiv_free` (a Kar
  complex in `[0, M]`, `M ≥ 1`, is Kar homotopy equivalent to a free one), `exists_free_pair`
  (`SymPair.transportD`: same boundary, free interior, `N ≥ 0`), `exists_free_nullCobordism`.
* Main results: `NegKStablyFree.exists_isometric_free`, `.exists_cls_free`,
  `.exists_free_of_lconc`, `.exists_free_pair`, `.exists_free_nullCobordism`, and the `NegK`
  versions.

**Blueprint check.**  The suggested proof is correct for `N ≥ 1` with one bookkeeping fix: the
elementary piece for `r = 0` must sit in degrees `(1, 0)` (not `(0, -1)`), as `negK.md` §1 says.
It is formalized degree by degree: after the step for degree `m`, every degree `< m` stays
Kar-free since `free ⊕ F` and `free ⊕ 0` are free.  Instead of "`E` null-cobordant + additivity"
we use that `P ⊂ P ⊕ E` is a homotopy isometry (`E.φ = 0` forces `E.p ≃ 0`), which gives
`P ≃ free`, not only equal classes.  For `N = 0` the blueprint argument does not
apply (no contractible piece lives in `[0, 0]`); the boundary trick above repairs it.  For
`N < 0` everything is `0`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v u

namespace Wall

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-! ### Kar isomorphisms -/

/-- A Kar isomorphism `(X, e) ≅ (Y, e')`: Kar morphisms `hom`, `inv` with `hom inv = e` and
`inv hom = e'` (idempotence of `e`, `e'` follows). -/
structure KarIso {X Y : V} (e : X ⟶ X) (e' : Y ⟶ Y) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  e_hom : e ≫ hom = hom
  hom_e : hom ≫ e' = hom
  e_inv : e' ≫ inv = inv
  inv_e : inv ≫ e = inv
  hom_inv : hom ≫ inv = e
  inv_hom : inv ≫ hom = e'

namespace KarIso

attribute [reassoc (attr := simp)] e_hom hom_e e_inv inv_e hom_inv inv_hom

variable {X Y Z : V} {e : X ⟶ X} {e' : Y ⟶ Y} {e'' : Z ⟶ Z}

/-- The identity of `(X, e)`. -/
@[simps]
def refl (he : e ≫ e = e) : KarIso e e :=
  ⟨e, e, he, he, he, he, he, he⟩

lemma inv_eq_zero (α : KarIso e e') (h : e = 0) : α.inv = 0 := by
  subst h; simpa using α.inv_e.symm

/-- Composition. -/
@[simps]
def trans (α : KarIso e e') (β : KarIso e' e'') : KarIso e e'' where
  hom := α.hom ≫ β.hom
  inv := β.inv ≫ α.inv
  e_hom := by simp
  hom_e := by simp
  e_inv := by simp
  inv_e := by simp
  hom_inv := by rw [assoc, β.hom_inv_assoc, α.hom_e_assoc, α.hom_inv]
  inv_hom := by rw [assoc, α.inv_hom_assoc, β.e_hom, β.inv_hom]

/-- Rewrite the idempotents. -/
@[simps]
def congr {f : X ⟶ X} {f' : Y ⟶ Y} (α : KarIso e e') (h : e = f) (h' : e' = f') : KarIso f f' :=
  ⟨α.hom, α.inv, h ▸ α.e_hom, h' ▸ α.hom_e, h' ▸ α.e_inv, h ▸ α.inv_e, h ▸ α.hom_inv,
    h' ▸ α.inv_hom⟩

/-- `(X, 0) ≅ (Y, 0)`. -/
@[simps]
def zero : KarIso (0 : X ⟶ X) (0 : Y ⟶ Y) :=
  ⟨0, 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Direct sums of Kar isomorphisms along arbitrary bicones. -/
@[simps]
def sum {X' Y' : V} {f : X' ⟶ X'} {f' : Y' ⟶ Y'} (α : KarIso e e') (β : KarIso f f')
    (b : BinaryBicone X X') (c : BinaryBicone Y Y') :
    KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ f ≫ b.inr) (c.fst ≫ e' ≫ c.inl + c.snd ≫ f' ≫ c.inr) where
  hom := b.fst ≫ α.hom ≫ c.inl + b.snd ≫ β.hom ≫ c.inr
  inv := c.fst ≫ α.inv ≫ b.inl + c.snd ≫ β.inv ≫ b.inr
  e_hom := by simp [add_comp, comp_add]
  hom_e := by simp [add_comp, comp_add]
  e_inv := by simp [add_comp, comp_add]
  inv_e := by simp [add_comp, comp_add]
  hom_inv := by simp [add_comp, comp_add]
  inv_hom := by simp [add_comp, comp_add]

/-- `(X, e) ⊕ (X', 0) ≅ (Y, e')`. -/
@[simps]
def sumZero {X' : V} (α : KarIso e e') (b : BinaryBicone X X') :
    KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ 0 ≫ b.inr) e' where
  hom := b.fst ≫ α.hom
  inv := α.inv ≫ b.inl
  e_hom := by simp
  hom_e := by simp
  e_inv := by simp
  inv_e := by simp
  hom_inv := by simp
  inv_hom := by simp

variable [HasBinaryBiproducts V]

/-- A witness of `KarStablyFree e F F'` as a Kar isomorphism `(M ⊞ F, e ⊞ 1) ≅ (F', 1)`. -/
@[simps]
def ofStablyFree {M F F' : V} {e : M ⟶ M} {u : M ⊞ F ⟶ F'} {v : F' ⟶ M ⊞ F}
    (huv : u ≫ v = biprod.map e (𝟙 F)) (hvu : v ≫ u = 𝟙 F') :
    KarIso (biprod.map e (𝟙 F)) (𝟙 F') where
  hom := u
  inv := v
  e_hom := by rw [← huv, assoc, hvu, comp_id]
  hom_e := comp_id u
  e_inv := id_comp v
  inv_e := by rw [← huv, ← assoc, hvu, id_comp]
  hom_inv := huv
  inv_hom := hvu

/-- **Absorption**: if `(M, e) ⊕ F ≅ F'`, then `(M, e) ⊕_b F` is free for any bicone `b`. -/
def absorb {M F F' : V} {e : M ⟶ M} (he : e ≫ e = e) {u : M ⊞ F ⟶ F'} {v : F' ⟶ M ⊞ F}
    (huv : u ≫ v = biprod.map e (𝟙 F)) (hvu : v ≫ u = 𝟙 F') (b : BinaryBicone M F) :
    KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ b.inr) (𝟙 F') :=
  ((sum (refl he) (refl (id_comp (𝟙 F))) b (BinaryBiproduct.bicone M F)).congr
    (by simp) (by simp [biprod.map_eq])).trans (ofStablyFree huv hvu)

/-- **Absorption into a sum**: if `(M, e) ⊕ F ≅ F'` and `G = F ⊕ F''` (bicone `c`), then
`(M, e) ⊕_b G ≅ F' ⊞ F''` is free. -/
def absorbSum {M F F' F'' : V} {e : M ⟶ M} (he : e ≫ e = e) {u : M ⊞ F ⟶ F'}
    {v : F' ⟶ M ⊞ F} (huv : u ≫ v = biprod.map e (𝟙 F)) (hvu : v ≫ u = 𝟙 F')
    (c : BinaryBicone F F'') (hc : c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt)
    (b : BinaryBicone M c.pt) :
    KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ b.inr) (𝟙 (F' ⊞ F'')) := by
  have hb : b.snd ≫ b.inr = b.snd ≫ c.fst ≫ c.inl ≫ b.inr + b.snd ≫ c.snd ≫ c.inr ≫ b.inr := by
    rw [← comp_add, ← assoc c.fst, ← assoc c.snd, ← add_comp, hc, id_comp]
  have he' {T : V} (h : M ⟶ T) : e ≫ e ≫ h = e ≫ h := by rw [← assoc, he]
  have huv' {T : V} (h : M ⊞ F ⟶ T) : u ≫ v ≫ h = biprod.map e (𝟙 F) ≫ h := by
    rw [← assoc, huv]
  have hv' {T : V} (h : M ⊞ F ⟶ T) :
      v ≫ biprod.fst ≫ e ≫ biprod.inl ≫ h + v ≫ biprod.snd ≫ biprod.inr ≫ h = v ≫ h := by
    have hv : v ≫ biprod.map e (𝟙 F) = v := (ofStablyFree huv hvu).inv_e
    conv_rhs => rw [← hv]
    simp [biprod.map_eq, add_comp, comp_add]
  refine
    { hom := (b.fst ≫ e ≫ biprod.inl + b.snd ≫ c.fst ≫ biprod.inr) ≫ u ≫ biprod.inl +
        b.snd ≫ c.snd ≫ biprod.inr
      inv := biprod.fst ≫ v ≫ (biprod.fst ≫ e ≫ b.inl + biprod.snd ≫ c.inl ≫ b.inr) +
        biprod.snd ≫ c.inr ≫ b.inr
      e_hom := ?_
      hom_e := by simp
      e_inv := by simp
      inv_e := ?_
      hom_inv := ?_
      inv_hom := ?_ }
  · simp [add_comp, comp_add, he']
  · simp [add_comp, comp_add, he', add_assoc]
  · simp only [add_comp, comp_add, assoc, BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc,
      BinaryBicone.inr_fst_assoc, BinaryBicone.inr_snd_assoc, zero_comp, comp_zero, add_zero,
      zero_add, huv', biprod.map_eq, he', id_comp]
    rw [hb]; abel
  · apply biprod.hom_ext'
    · simp only [add_comp, comp_add, assoc, BinaryBicone.inl_fst_assoc,
        BinaryBicone.inl_snd_assoc, BinaryBicone.inr_fst_assoc, BinaryBicone.inr_snd_assoc,
        zero_comp, comp_zero, add_zero, zero_add, he', comp_id]
      rw [hv', reassoc_of% hvu]
    · simp [add_comp, comp_add]

end KarIso

/-! ### Elementary contractible complexes -/

/-- `F` in every degree, with `d_{s, s-1} = 1` and all other differentials `0`. -/
@[simps, implicit_reducible]
def elemComplex (F : V) (s : ℤ) : ChainComplex V ℤ where
  X _ := F
  d i j := if i = s ∧ j = s - 1 then 𝟙 F else 0
  shape i j h := by
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h (by simp)
  d_comp_d' i j k _ _ := by
    split_ifs with h₁ h₂
    · exfalso; omega
    all_goals simp

/-- The chain idempotent `1` in degrees `s`, `s - 1`: the elementary Kar complex `F → F`. -/
@[simps]
def elemIdem (F : V) (s : ℤ) : elemComplex F s ⟶ elemComplex F s where
  f i := if i = s ∨ i = s - 1 then 𝟙 F else 0
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    simp only [elemComplex_d]
    split_ifs <;> first | (exfalso; omega) | simp

lemma elemIdem_idem (F : V) (s : ℤ) : elemIdem F s ≫ elemIdem F s = elemIdem F s := by
  ext i
  simp only [comp_f, elemIdem_f]
  split_ifs <;> simp

lemma elemIdem_support (F : V) {s lo hi : ℤ} (h₁ : lo ≤ s - 1) (h₂ : s ≤ hi) :
    SupportedIn (elemIdem F s) lo hi := fun r hr ↦ by
  rw [elemIdem_f, if_neg (by omega)]

/-- The contraction `h_{s-1 → s} = 1` of the elementary complex. -/
@[simps]
def elemHomotopy (F : V) (s : ℤ) : Homotopy (elemIdem F s) 0 where
  hom i j := if i = s - 1 ∧ j = s then 𝟙 F else 0
  zero i j hij := by
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij (by simp)
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp)]
    simp only [elemComplex_d, elemIdem_f, zero_f, add_zero]
    split_ifs <;> first | (exfalso; omega) | simp

/-! ### Degreewise bookkeeping of one step -/

/-- The degree-`r` object `(C_r, p_r)` of a Kar complex is Kar-isomorphic to a free object. -/
def KarFree {C : ChainComplex V ℤ} (p : C ⟶ C) (r : ℤ) : Prop :=
  ∃ F : V, Nonempty (KarIso (p.f r) (𝟙 F))

lemma f_idem {C : ChainComplex V ℤ} {p : C ⟶ C} (hp : p ≫ p = p) (r : ℤ) :
    p.f r ≫ p.f r = p.f r := by
  rw [← comp_f, hp]

/-- Off the absorbing degree: `free ⊕ (F, elemIdem_r)` is free (`free ⊕ F` or `free ⊕ 0`). -/
lemma karFree_sumElem_of_karFree [HasBinaryBiproducts V] {X F G : V} {e : X ⟶ X}
    (α : KarIso e (𝟙 G)) (s r : ℤ) (b : BinaryBicone X F) :
    ∃ G' : V, Nonempty (KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ (elemIdem F s).f r ≫ b.inr) (𝟙 G')) := by
  by_cases hr : r = s ∨ r = s - 1
  · refine ⟨G ⊞ F, ⟨(KarIso.sum α (KarIso.refl (id_comp (𝟙 F))) b
      (BinaryBiproduct.bicone G F)).congr ?_ ?_⟩⟩
    · rw [elemIdem_f, if_pos hr]
    · simp [biprod.total]
  · refine ⟨G, ⟨(KarIso.sumZero α b).congr ?_ rfl⟩⟩
    rw [elemIdem_f, if_neg hr]

/-- At the absorbing degree: `(X, e) ⊕ (F, 1)` is free if `(X, e) ⊕ F ≅ F'`. -/
lemma karFree_sumElem_self [HasBinaryBiproducts V] {X F F' : V} {e : X ⟶ X} (he : e ≫ e = e)
    (h : KarStablyFree e F F') {s m : ℤ} (hms : m = s ∨ m = s - 1) (b : BinaryBicone X F) :
    ∃ G' : V, Nonempty (KarIso (b.fst ≫ e ≫ b.inl + b.snd ≫ (elemIdem F s).f m ≫ b.inr) (𝟙 G')) := by
  obtain ⟨u, v, huv, hvu⟩ := h
  refine ⟨F', ⟨(KarIso.absorb he huv hvu b).congr ?_ rfl⟩⟩
  rw [elemIdem_f, if_pos hms, id_comp]

/-- The elementary piece sits in degrees `(s, s - 1) ⊂ [0, M]` and covers degree `m ∈ [0, M]`. -/
lemma exists_elem_degree {M m : ℤ} (hM : 1 ≤ M) (hm₀ : 0 ≤ m) (hmM : m ≤ M) :
    ∃ s : ℤ, 1 ≤ s ∧ s ≤ M ∧ (m = s ∨ m = s - 1) := by
  by_cases h : m = 0
  · exact ⟨1, le_rfl, hM, Or.inr (by omega)⟩
  · exact ⟨m, by omega, hmM, Or.inl rfl⟩

/-! ### Symmetric complexes with zero structure -/

variable {J : StrictInvolution V} {N : ℤ}

/-- `(C, p, 0)` is Poincaré when `p ≃ 0` (a contractible Kar complex with zero structure). -/
@[simps, implicit_reducible]
def ofNullHomotopic (C : ChainComplex V ℤ) (p : C ⟶ C) (hp : p ≫ p = p)
    (hs : SupportedIn p 0 N) (H : Homotopy p 0) : SymPoincare J N where
  C := C
  p := p
  p_idem := hp
  support := hs
  φ := 0
  φ_kar := by simp
  symm := by simp [IsStrictSymm, transposeHom_zero]
  poincare := ⟨0, by simp, ⟨homotopyCongr H.symm (by simp) rfl⟩,
    ⟨homotopyCongr (dualHomotopy J N H).symm (by simp [dualHom_zero]) rfl⟩⟩

/-- The elementary piece `F → F` in degrees `(s, s - 1)`, `1 ≤ s ≤ N`, with zero structure. -/
abbrev elem (F : V) {s : ℤ} (h₁ : 1 ≤ s) (h₂ : s ≤ N) : SymPoincare J N :=
  ofNullHomotopic (elemComplex F s) (elemIdem F s) (elemIdem_idem F s)
    (elemIdem_support F (by omega) h₂) (elemHomotopy F s)

lemma sum_p_f (P Q : SymPoincare J N) (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) (r : ℤ) :
    (P.sum Q b).p.f r = (b r).fst ≫ P.p.f r ≫ (b r).inl + (b r).snd ≫ Q.p.f r ≫ (b r).inr := by
  simp

/-- **Adding a summand with zero structure** does not change the homotopy isometry class: if
`E.φ = 0`, Poincaré duality forces `E.p ≃ 0`, and `P ⊂ P ⊕ E` is a homotopy isometry. -/
theorem isometric_sum_of_φ_eq_zero (P E : SymPoincare J N) (hE : E.φ = 0)
    (b : ∀ r, BinaryBicone (P.C.X r) (E.C.X r)) : P.Isometric (P.sum E b) := by
  obtain ⟨ψ, -, ⟨H⟩, -⟩ := E.poincare
  have H' : Homotopy 0 E.p := homotopyCongr H (by simp [hE]) rfl
  exact ⟨⟨P.p ≫ sumInl b, sumFst b ≫ P.p, by simp, by simp, .ofEq (by simp),
    homotopyCongr ((Homotopy.refl (sumFst b ≫ P.p ≫ sumInl b)).add
      ((H'.compLeft (sumSnd b)).compRight (sumInr b))) (by simp) (by simp),
    .ofEq (by simp [hE])⟩⟩

/-! ### Strict transport along degreewise Kar isomorphisms -/

section Transport

variable {C : ChainComplex V ℤ} (p : C ⟶ C) {X : ℤ → V} {q : ∀ r, X r ⟶ X r}
  (α : ∀ r, KarIso (p.f r) (q r))

/-- The complex `(X_r, α_r⁻¹ d α_{r-1})`. -/
@[simps, implicit_reducible]
def transportComplex : ChainComplex V ℤ where
  X := X
  d i j := (α i).inv ≫ C.d i j ≫ (α j).hom
  shape i j h := by simp [C.shape i j h]
  d_comp_d' i j k _ _ := by
    simp only [assoc, KarIso.hom_inv_assoc]
    rw [← p.comm_assoc, C.d_comp_d_assoc, zero_comp, comp_zero, comp_zero]

/-- `α` as a chain map. -/
@[simps]
def transportHom : C ⟶ transportComplex p α where
  f r := (α r).hom
  comm' i j _ := by
    simp only [transportComplex_d, KarIso.hom_inv_assoc]
    rw [p.comm_assoc, KarIso.e_hom]

/-- `α⁻¹` as a chain map. -/
@[simps]
def transportInv : transportComplex p α ⟶ C where
  f r := (α r).inv
  comm' i j _ := by
    simp only [transportComplex_d, assoc, KarIso.hom_inv]
    rw [← p.comm, KarIso.inv_e_assoc]

@[reassoc (attr := simp)]
lemma transportHom_transportInv : transportHom p α ≫ transportInv p α = p := by
  ext r; simp

@[reassoc (attr := simp)]
lemma p_transportHom : p ≫ transportHom p α = transportHom p α := by
  ext r; simp

@[reassoc (attr := simp)]
lemma transportInv_p : transportInv p α ≫ p = transportInv p α := by
  ext r; simp

/-- The transported idempotent `α⁻¹ α`, which is `q` degreewise. -/
abbrev transportIdem : transportComplex p α ⟶ transportComplex p α :=
  transportInv p α ≫ transportHom p α

lemma transportIdem_f (r : ℤ) : (transportIdem p α).f r = q r := by
  simp

lemma transportIdem_idem : transportIdem p α ≫ transportIdem p α = transportIdem p α := by
  simp

lemma transportIdem_support {lo hi : ℤ} (hs : SupportedIn p lo hi) :
    SupportedIn (transportIdem p α) lo hi := fun r hr ↦ by
  simp [(α r).inv_eq_zero (hs r hr)]

@[reassoc (attr := simp)]
lemma dualHom_transportInv_dualHom_transportHom :
    dualHom J N (transportInv p α) ≫ dualHom J N (transportHom p α) = dualHom J N p := by
  rw [← dualHom_comp, transportHom_transportInv]

@[reassoc (attr := simp)]
lemma dualHom_p_dualHom_transportInv :
    dualHom J N p ≫ dualHom J N (transportInv p α) = dualHom J N (transportInv p α) := by
  rw [← dualHom_comp, transportInv_p]

variable (P : SymPoincare J N) (β : ∀ r, KarIso (P.p.f r) (q r))

/-- **Strict transport** of a Poincaré complex: `(X, q, β φ β^*)`, where
`(C_r, p_r) ≅ (X_r, q_r)` by `β_r`. -/
@[simps, implicit_reducible]
def strictTransport : SymPoincare J N where
  C := transportComplex P.p β
  p := transportIdem P.p β
  p_idem := transportIdem_idem P.p β
  support := transportIdem_support P.p β P.support
  φ := dualHom J N (transportHom P.p β) ≫ P.φ ≫ transportHom P.p β
  φ_kar := by simp
  symm := P.symm.conj _
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    have hψ' : P.p ≫ ψ = ψ := by rw [← hψ]; simp
    refine ⟨transportInv P.p β ≫ ψ ≫ dualHom J N (transportInv P.p β), ?_,
      ⟨homotopyCongr ((H₁.compLeft (transportInv P.p β)).compRight (transportHom P.p β))
        (by simp) (by simp)⟩,
      ⟨homotopyCongr ((H₂.compLeft (dualHom J N (transportHom P.p β))).compRight
        (dualHom J N (transportInv P.p β))) (by simp [reassoc_of% hψ']) (by simp)⟩⟩
    simp only [dualHom_comp, assoc, transportHom_transportInv_assoc, transportInv_p_assoc,
      dualHom_transportInv_dualHom_transportHom_assoc, dualHom_p_dualHom_transportInv]

lemma strictTransport_p_f (r : ℤ) : (strictTransport P β).p.f r = q r :=
  transportIdem_f P.p β r

/-- The strict isometry `P ≃ strictTransport P β`. -/
def strictTransportIsometry : P.HomotopyIsometry (strictTransport P β) :=
  .ofEq (transportHom P.p β) (transportInv P.p β) (by simp) (by simp) (by simp) rfl rfl

end Transport

/-! ### The Wall trick in dimensions `N ≥ 1` -/

section Main

variable [HasBinaryBiproducts V]

/-- Every object of `Kar V` is stably free: `(M, e) ⊕ F ≅ F'` with `F`, `F'` free
(`NegKStablyFree` at one level). -/
def StablyFreeObjects (V : Type u) [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V] :
    Prop :=
  ∀ (M : V) (e : M ⟶ M), e ≫ e = e → ∃ F F' : V, KarStablyFree e F F'

/-- **One step of the Wall trick.**  Adding the elementary piece on `F` in degrees `(s, s - 1)`
(`s = m`, or `s = 1` if `m = 0`), where `(C_m, p_m) ⊕ F ≅ F'`, makes degree `m` free and keeps
every Kar-free degree Kar-free. -/
theorem exists_step (hK : StablyFreeObjects V) (hN : 1 ≤ N) (Q : SymPoincare J N) {m : ℤ}
    (hm₀ : 0 ≤ m) (hmN : m ≤ N) :
    ∃ Q' : SymPoincare J N, Q.Isometric Q' ∧ KarFree Q'.p m ∧
      ∀ r, KarFree Q.p r → KarFree Q'.p r := by
  obtain ⟨F, F', hF⟩ := hK (Q.C.X m) (Q.p.f m) (f_idem Q.p_idem m)
  obtain ⟨s, hs₁, hsN, hms⟩ := exists_elem_degree hN hm₀ hmN
  let E : SymPoincare J N := elem F hs₁ hsN
  let b : ∀ r, BinaryBicone (Q.C.X r) (E.C.X r) := fun r ↦ BinaryBiproduct.bicone _ _
  refine ⟨Q.sum E b, isometric_sum_of_φ_eq_zero Q E rfl b, ?_, ?_⟩
  · simp only [KarFree, sum_p_f]
    exact karFree_sumElem_self (f_idem Q.p_idem m) hF hms (b m)
  · rintro r ⟨G, ⟨α⟩⟩
    simp only [KarFree, sum_p_f]
    exact karFree_sumElem_of_karFree α s r (b r)

/-- **The Wall trick, Kar form** (`N ≥ 1`): `P` is homotopy isometric to a complex whose chain
objects in degrees `[0, N]` are all Kar-isomorphic to free objects. -/
theorem exists_isometric_karFree (hK : StablyFreeObjects V) (hN : 1 ≤ N) (P : SymPoincare J N) :
    ∃ Q : SymPoincare J N, P.Isometric Q ∧ ∀ r, 0 ≤ r → r ≤ N → KarFree Q.p r := by
  have key : ∀ m : ℕ, (m : ℤ) ≤ N + 1 → ∃ Q : SymPoincare J N, P.Isometric Q ∧
      ∀ r : ℤ, 0 ≤ r → r < m → KarFree Q.p r := by
    intro m
    induction m with
    | zero => exact fun _ ↦ ⟨P, ⟨.refl P⟩, fun r h₀ h₁ ↦ by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨Q, hPQ, hQ⟩ := ih (by omega)
      obtain ⟨Q', hQQ', hm', hfree⟩ := exists_step hK hN Q (m := m) (by omega) (by omega)
      refine ⟨Q', SymPoincare.isometric_equivalence.trans hPQ hQQ', fun r h₀ h₁ ↦ ?_⟩
      rcases lt_or_eq_of_le (show r ≤ m by omega) with h | rfl
      · exact hfree r (hQ r h₀ h)
      · exact hm'
  obtain ⟨Q, hPQ, hQ⟩ := key (N + 1).toNat (by omega)
  exact ⟨Q, hPQ, fun r h₀ h₁ ↦ hQ r h₀ (by omega)⟩

omit [HasBinaryBiproducts V] in
/-- Kar targets: free objects on `[lo, hi]`, `(C_r, 0)` elsewhere. -/
lemma exists_karIso_targets {C : ChainComplex V ℤ} (p : C ⟶ C) {lo hi : ℤ}
    (hs : SupportedIn p lo hi) (hP : ∀ r, lo ≤ r → r ≤ hi → KarFree p r) (r : ℤ) :
    ∃ (X : V) (q : X ⟶ X), Nonempty (KarIso (p.f r) q) ∧ (lo ≤ r → r ≤ hi → q = 𝟙 X) := by
  by_cases hr : lo ≤ r ∧ r ≤ hi
  · obtain ⟨F, hF⟩ := hP r hr.1 hr.2
    exact ⟨F, 𝟙 F, hF, fun _ _ ↦ rfl⟩
  · exact ⟨C.X r, 0, ⟨(KarIso.zero (X := C.X r) (Y := C.X r)).congr
      (hs r (by omega)).symm rfl⟩, fun h₀ h₁ ↦ absurd ⟨h₀, h₁⟩ hr⟩

omit [HasBinaryBiproducts V] in
/-- A complex that is Kar-free in every degree of `[0, N]` is strictly isometric to a free one
(idempotent `1` on `[0, N]`). -/
theorem exists_isometric_free_of_karFree (P : SymPoincare J N)
    (hP : ∀ r, 0 ≤ r → r ≤ N → KarFree P.p r) :
    ∃ Q : SymPoincare J N, P.Isometric Q ∧ ∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _ := by
  choose X q hα hq using exists_karIso_targets P.p P.support hP
  exact ⟨strictTransport P (fun r ↦ (hα r).some), ⟨strictTransportIsometry P _⟩,
    fun r h₀ h₁ ↦ by rw [strictTransport_p_f]; exact hq r h₀ h₁⟩

/-- **The symmetric Wall trick** (`N ≥ 1`): if every object of `Kar V` is stably free, every
`N`-dimensional Poincaré complex is homotopy isometric to a free one. -/
theorem exists_isometric_free (hK : StablyFreeObjects V) (hN : 1 ≤ N) (P : SymPoincare J N) :
    ∃ Q : SymPoincare J N, P.Isometric Q ∧ ∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _ := by
  obtain ⟨Q, hPQ, hQ⟩ := exists_isometric_karFree hK hN P
  obtain ⟨Q', hQQ', hQ'⟩ := exists_isometric_free_of_karFree Q hQ
  exact ⟨Q', SymPoincare.isometric_equivalence.trans hPQ hQQ', hQ'⟩

end Main

/-! ### Dimension `0`: the boundary trick -/

section DimZero

variable [HasBinaryBiproducts V]

/-- `F` in every degree, with zero differential. -/
@[simps, implicit_reducible]
def constComplex (F : V) : ChainComplex V ℤ where
  X _ := F
  d _ _ := 0

/-- The chain idempotent `1` in degree `s` only. -/
@[simps]
def singleIdem (F : V) (s : ℤ) : constComplex F ⟶ constComplex F where
  f i := if i = s then 𝟙 F else 0

variable (J) in
/-- The `1`-dimensional symmetric complex `(F[1], 0)` (not Poincaré). -/
@[simps, implicit_reducible]
def shiftedZero (F : V) : SymComplex J (0 + 1) where
  C := constComplex F
  p := singleIdem F 1
  p_idem := by
    ext i
    simp only [comp_f, singleIdem_f]
    split_ifs <;> simp
  φ := 0
  φ_kar := by simp
  symm := by simp [IsStrictSymm, transposeHom_zero]

omit [HasBinaryBiproducts V] in
lemma shiftedZero_support (F : V) : SupportedIn (shiftedZero J F).p 1 (0 + 1) := fun r hr ↦ by
  simp only [shiftedZero_p, singleIdem_f]
  rw [if_neg (by omega)]

variable (J) in
/-- `∂(F[1], 0)`: a `0`-dimensional Poincaré complex on `F ⊕ F` (hyperbolic), null-cobordant by
`SymComplex.nullCobordant_boundary`. -/
abbrev hypBoundary (F : V) : SymPoincare J 0 :=
  (shiftedZero J F).boundary (shiftedZero_support F)

lemma hypBoundary_p_f_zero (F : V) : (hypBoundary J F).p.f 0 = 𝟙 _ := by
  simp only [SymComplex.boundary_p, desuspMap_f]
  rw [coneMap_f _ (0 + 1) 0 (by simp), dualHom_f, shiftedZero_p, singleIdem_f, singleIdem_f,
    if_pos (by norm_num), if_pos (by norm_num)]
  erw [J.star_id, id_comp, id_comp]
  exact (cone.id_X _ (0 + 1) 0 _).symm

variable (J) in
/-- `∂C_0 = C^1 ⊕ C_1 = F ⊕ F`: the summands `fstX`, `sndX` of `Cone(0)_1`. -/
@[simps]
def hypBicone (F : V) : BinaryBicone F F where
  pt := (hypBoundary J F).C.X 0
  fst := homotopyCofiber.fstX (shiftedZero J F).φ (0 + 1) 0 (by simp)
  snd := homotopyCofiber.sndX (shiftedZero J F).φ (0 + 1)
  inl := homotopyCofiber.inlX (shiftedZero J F).φ 0 (0 + 1) (by simp)
  inr := homotopyCofiber.inrX (shiftedZero J F).φ (0 + 1)
  inl_fst := homotopyCofiber.inlX_fstX _ _ _ _
  inl_snd := homotopyCofiber.inlX_sndX _ _ _ _
  inr_fst := homotopyCofiber.inrX_fstX _ _ _ _
  inr_snd := homotopyCofiber.inrX_sndX _ _

lemma hypBicone_total (F : V) :
    (hypBicone J F).fst ≫ (hypBicone J F).inl + (hypBicone J F).snd ≫ (hypBicone J F).inr =
      𝟙 _ :=
  (cone.id_X _ (0 + 1) 0 _).symm

/-- **Dimension `0`.**  If `(C_0, p_0) ⊕ F ≅ F'`, then `P ⊕ ∂(F[1], 0)` is Kar-free in
degree `0`: `(C_0, p_0) ⊕ (F ⊕ F) ≅ F' ⊕ F`. -/
theorem exists_karFree_sum_hypBoundary (hK : StablyFreeObjects V) (P : SymPoincare J 0) :
    ∃ (F : V) (b : ∀ r, BinaryBicone (P.C.X r) ((hypBoundary J F).C.X r)),
      KarFree (P.sum (hypBoundary J F) b).p 0 := by
  obtain ⟨F, F', u, v, huv, hvu⟩ := hK (P.C.X 0) (P.p.f 0) (f_idem P.p_idem 0)
  let b : ∀ r, BinaryBicone (P.C.X r) ((hypBoundary J F).C.X r) :=
    fun r ↦ BinaryBiproduct.bicone _ _
  refine ⟨F, b, F' ⊞ F, ⟨(KarIso.absorbSum (f_idem P.p_idem 0) huv hvu (hypBicone J F)
    (hypBicone_total F) (b 0)).congr ?_ rfl⟩⟩
  rw [sum_p_f, hypBoundary_p_f_zero]
  erw [id_comp] <;> rfl

end DimZero

/-! ### Classes in `Lconc` -/

/-- **Dimension `0`**: `[P] = [P ⊕ ∂(F[1], 0)]` is the class of a free complex.  (`P` itself
need not be isometric to a free complex: `(C_0, p_0)` is only stably free.) -/
theorem exists_cls_free_dim_zero {A : InvCat} (hK : StablyFreeObjects A)
    (P : SymPoincare A.inv 0) :
    ∃ Q : SymPoincare A.inv 0, Q.p.f 0 = 𝟙 _ ∧ Lconc.cls Q = Lconc.cls P := by
  obtain ⟨F, b, hb⟩ := exists_karFree_sum_hypBoundary hK P
  obtain ⟨Q, hQ, hQf⟩ := exists_isometric_free_of_karFree (P.sum _ b) fun r h₀ h₁ ↦ by
    obtain rfl : r = 0 := by omega
    exact hb
  refine ⟨Q, hQf 0 le_rfl le_rfl, ?_⟩
  rw [← Lconc.cls_eq_of_isometric hQ, Lconc.cls_sum,
    Lconc.cls_eq_zero (SymComplex.nullCobordant_boundary _ _), add_zero]

/-- **The symmetric Wall trick, all dimensions**: if every object of `Kar A` is stably free,
every class of `Lconc A N` is represented by a free complex. -/
theorem exists_cls_free {A : InvCat} (hK : StablyFreeObjects A) {N : ℤ}
    (P : SymPoincare A.inv N) :
    ∃ Q : SymPoincare A.inv N, (∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _) ∧
      Lconc.cls Q = Lconc.cls P := by
  rcases lt_trichotomy N 0 with hN | rfl | hN
  · exact ⟨P, fun r h₀ h₁ ↦ absurd (h₀.trans h₁) (by omega), rfl⟩
  · obtain ⟨Q, hQ, hcls⟩ := exists_cls_free_dim_zero hK P
    exact ⟨Q, fun r h₀ h₁ ↦ by obtain rfl : r = 0 := by omega
                               exact hQ, hcls⟩
  · obtain ⟨Q, hPQ, hQ⟩ := exists_isometric_free hK (by omega) P
    exact ⟨Q, hQ, (Lconc.cls_eq_of_isometric hPQ).symm⟩

/-! ### Kar complexes and pairs: the relative Wall trick -/

section Pairs

/-- The idempotent `p ⊕ e` of `D ⊕ E`, `E` the elementary piece on `F` in degrees `(s, s - 1)`. -/
abbrev sumElemIdem {D : ChainComplex V ℤ} (pD : D ⟶ D) (F : V) (s : ℤ)
    (b : ∀ r, BinaryBicone (D.X r) ((elemComplex F s).X r)) : sumComplex b ⟶ sumComplex b :=
  sumFst b ≫ pD ≫ sumInl b + sumSnd b ≫ elemIdem F s ≫ sumInr b

section SumElem

variable {D : ChainComplex V ℤ} {pD : D ⟶ D} (hpD : pD ≫ pD = pD) (F : V) (s : ℤ)
  (b : ∀ r, BinaryBicone (D.X r) ((elemComplex F s).X r))
include hpD

lemma sumElemIdem_idem :
    sumElemIdem pD F s b ≫ sumElemIdem pD F s b = sumElemIdem pD F s b := by
  simp [add_comp, comp_add, reassoc_of% hpD, reassoc_of% (elemIdem_idem F s)]

omit hpD in
lemma sumElemIdem_f (r : ℤ) : (sumElemIdem pD F s b).f r =
    (b r).fst ≫ pD.f r ≫ (b r).inl + (b r).snd ≫ (elemIdem F s).f r ≫ (b r).inr := by
  simp

omit hpD in
lemma sumElemIdem_support {M : ℤ} (hs : SupportedIn pD 0 M) (h₁ : 1 ≤ s) (h₂ : s ≤ M) :
    SupportedIn (sumElemIdem pD F s b) 0 M := fun r hr ↦ by
  rw [sumElemIdem_f, hs r hr, elemIdem_support F (by omega) h₂ r hr]
  simp

/-- `(D, p) ≃ (D ⊕ E, p ⊕ e)` in `Kar`: the elementary piece is contractible. -/
def karHtpyEquivSumElem : KarHtpyEquiv pD (sumElemIdem pD F s b) where
  f := pD ≫ sumInl b
  g := sumFst b ≫ pD
  pf := by rw [reassoc_of% hpD]
  fp := by simp [comp_add, reassoc_of% hpD]
  pg := by simp [add_comp, hpD]
  gp := by rw [assoc, hpD]
  fg := .ofEq (by simp [hpD])
  gf := homotopyCongr ((Homotopy.refl (sumFst b ≫ pD ≫ sumInl b)).add
      (((elemHomotopy F s).symm.compLeft (sumSnd b)).compRight (sumInr b)))
    (by simp [reassoc_of% hpD]) (by simp)

end SumElem

section KarTransport

variable {C : ChainComplex V ℤ} (p : C ⟶ C) {X : ℤ → V} {q : ∀ r, X r ⟶ X r}
  (α : ∀ r, KarIso (p.f r) (q r))

/-- The strict transport as a Kar homotopy equivalence `(C, p) ≃ (X, q)`. -/
@[simps]
def transportKarHtpyEquiv : KarHtpyEquiv p (transportIdem p α) where
  f := transportHom p α
  g := transportInv p α
  pf := p_transportHom p α
  fp := by simp
  pg := by simp
  gp := transportInv_p p α
  fg := .ofEq (transportHom_transportInv p α)
  gf := Homotopy.refl _

end KarTransport

variable [HasBinaryBiproducts V] {D : ChainComplex V ℤ} {pD : D ⟶ D}

/-- **One step for a Kar complex** (no structure): add an elementary piece absorbing degree `m`. -/
theorem exists_karStep (hK : StablyFreeObjects V) {M : ℤ} (hM : 1 ≤ M) (hpD : pD ≫ pD = pD)
    (hs : SupportedIn pD 0 M) {m : ℤ} (hm₀ : 0 ≤ m) (hmM : m ≤ M) :
    ∃ (D' : ChainComplex V ℤ) (pD' : D' ⟶ D'), pD' ≫ pD' = pD' ∧ SupportedIn pD' 0 M ∧
      Nonempty (KarHtpyEquiv pD pD') ∧ KarFree pD' m ∧ ∀ r, KarFree pD r → KarFree pD' r := by
  obtain ⟨F, F', hF⟩ := hK (D.X m) (pD.f m) (f_idem hpD m)
  obtain ⟨s, hs₁, hsM, hms⟩ := exists_elem_degree hM hm₀ hmM
  let b : ∀ r, BinaryBicone (D.X r) ((elemComplex F s).X r) := fun r ↦ BinaryBiproduct.bicone _ _
  refine ⟨_, sumElemIdem pD F s b, sumElemIdem_idem hpD F s b,
    sumElemIdem_support F s b hs hs₁ hsM, ⟨karHtpyEquivSumElem hpD F s b⟩, ?_, ?_⟩
  · simp only [KarFree, sumElemIdem_f]
    exact karFree_sumElem_self (f_idem hpD m) hF hms (b m)
  · rintro r ⟨G, ⟨α⟩⟩
    simp only [KarFree, sumElemIdem_f]
    exact karFree_sumElem_of_karFree α s r (b r)

/-- **The Wall trick for Kar complexes** (`M ≥ 1`): a Kar complex supported in `[0, M]` is Kar
homotopy equivalent to one, supported in `[0, M]`, with every degree Kar-free. -/
theorem exists_karHtpyEquiv_karFree (hK : StablyFreeObjects V) {M : ℤ} (hM : 1 ≤ M)
    (hpD : pD ≫ pD = pD) (hs : SupportedIn pD 0 M) :
    ∃ (D' : ChainComplex V ℤ) (pD' : D' ⟶ D'), pD' ≫ pD' = pD' ∧ SupportedIn pD' 0 M ∧
      Nonempty (KarHtpyEquiv pD pD') ∧ ∀ r, 0 ≤ r → r ≤ M → KarFree pD' r := by
  have key : ∀ m : ℕ, (m : ℤ) ≤ M + 1 → ∃ (D' : ChainComplex V ℤ) (pD' : D' ⟶ D'),
      pD' ≫ pD' = pD' ∧ SupportedIn pD' 0 M ∧ Nonempty (KarHtpyEquiv pD pD') ∧
        ∀ r : ℤ, 0 ≤ r → r < m → KarFree pD' r := by
    intro m
    induction m with
    | zero => exact fun _ ↦ ⟨D, pD, hpD, hs, ⟨.refl hpD⟩, fun r h₀ h₁ ↦ by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨D₁, p₁, hp₁, hs₁, ⟨e₁⟩, hfree₁⟩ := ih (by omega)
      obtain ⟨D₂, p₂, hp₂, hs₂, ⟨e₂⟩, hm₂, hfree₂⟩ :=
        exists_karStep hK hM hp₁ hs₁ (m := m) (by omega) (by omega)
      refine ⟨D₂, p₂, hp₂, hs₂, ⟨e₁.trans e₂⟩, fun r h₀ h₁ ↦ ?_⟩
      rcases lt_or_eq_of_le (show r ≤ m by omega) with h | rfl
      · exact hfree₂ r (hfree₁ r h₀ h)
      · exact hm₂
  obtain ⟨D', pD', hpD', hs', e, hfree⟩ := key (M + 1).toNat (by omega)
  exact ⟨D', pD', hpD', hs', e, fun r h₀ h₁ ↦ hfree r h₀ (by omega)⟩

/-- **The Wall trick for Kar complexes, free form** (`M ≥ 1`): a Kar complex supported in
`[0, M]` is Kar homotopy equivalent to a free one (idempotent `1` on `[0, M]`). -/
theorem exists_karHtpyEquiv_free (hK : StablyFreeObjects V) {M : ℤ} (hM : 1 ≤ M)
    (hpD : pD ≫ pD = pD) (hs : SupportedIn pD 0 M) :
    ∃ (D' : ChainComplex V ℤ) (pD' : D' ⟶ D'), pD' ≫ pD' = pD' ∧ SupportedIn pD' 0 M ∧
      Nonempty (KarHtpyEquiv pD pD') ∧ ∀ r, 0 ≤ r → r ≤ M → pD'.f r = 𝟙 _ := by
  obtain ⟨D', pD', -, hs', ⟨e⟩, hfree⟩ := exists_karHtpyEquiv_karFree hK hM hpD hs
  choose X q hα hq using exists_karIso_targets pD' hs' hfree
  let α : ∀ r, KarIso (pD'.f r) (q r) := fun r ↦ (hα r).some
  exact ⟨_, transportIdem pD' α, transportIdem_idem pD' α, transportIdem_support pD' α hs',
    ⟨e.trans (transportKarHtpyEquiv pD' α)⟩,
    fun r h₀ h₁ ↦ by rw [transportIdem_f]; exact hq r h₀ h₁⟩

variable [HasFiniteBiproducts V]

/-- **The relative Wall trick** (`N ≥ 0`): every `(N+1)`-dimensional Poincaré pair can be
replaced by one with the **same boundary** and a free interior (idempotent `1` on `[0, N+1]`),
by `SymPair.transportD` along `exists_karHtpyEquiv_free`. -/
theorem exists_free_pair (hK : StablyFreeObjects V) (hN : 0 ≤ N) (X : SymPair J N) :
    ∃ X' : SymPair J N, X'.bd = X.bd ∧ ∀ r, 0 ≤ r → r ≤ N + 1 → X'.pD.f r = 𝟙 _ := by
  obtain ⟨D', pD', hpD', hs', ⟨e⟩, hfree⟩ :=
    exists_karHtpyEquiv_free hK (M := N + 1) (by omega) X.pD_idem X.support
  exact ⟨X.transportD e hpD' hs', rfl, hfree⟩

/-- A null-cobordant `P` (`N ≥ 0`) bounds a pair with free interior. -/
theorem exists_free_nullCobordism (hK : StablyFreeObjects V) (hN : 0 ≤ N)
    {P : SymPoincare J N} (hP : NullCobordant P) :
    ∃ X : SymPair J N, X.bd = P ∧ ∀ r, 0 ≤ r → r ≤ N + 1 → X.pD.f r = 𝟙 _ := by
  obtain ⟨X, rfl⟩ := hP
  exact exists_free_pair hK hN X

end Pairs

end Wall

/-! ### Under `NegK` -/

namespace NegKStablyFree

variable {B : InvCat} (hK : NegKStablyFree B) {k : ℕ} (hk : 1 ≤ k)
include hK hk

lemma stablyFreeObjects : Wall.StablyFreeObjects (B.czIter k) :=
  hK k hk

/-- **Symmetric Wall trick** (lower-L module 21, `N ≥ 1`): every `N`-dimensional Poincaré complex
over `Kar (C_ℤ^{∘k} B)`, `k ≥ 1`, is homotopy isometric to a free one. -/
theorem exists_isometric_free {N : ℤ} (hN : 1 ≤ N) (P : SymPoincare (B.czIter k).inv N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, P.Isometric Q ∧ ∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _ :=
  Wall.exists_isometric_free (hK.stablyFreeObjects hk) hN P

/-- **Symmetric Wall trick** (lower-L module 21): every Poincaré complex over
`Kar (C_ℤ^{∘k} B)`, `k ≥ 1`, has the same `Lconc` class as a free one. -/
theorem exists_cls_free {N : ℤ} (P : SymPoincare (B.czIter k).inv N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, (∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _) ∧
      Lconc.cls Q = Lconc.cls P :=
  Wall.exists_cls_free (hK.stablyFreeObjects hk) P

/-- Every element of `Lconc (C_ℤ^{∘k} B) N`, `k ≥ 1`, is the class of a free complex. -/
theorem exists_free_of_lconc {N : ℤ} (x : Lconc (B.czIter k) N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, (∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _) ∧
      Lconc.cls Q = x := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  exact hK.exists_cls_free hk P

/-- **Relative symmetric Wall trick** (`N ≥ 0`): every `(N+1)`-dimensional Poincaré pair over
`Kar (C_ℤ^{∘k} B)`, `k ≥ 1`, can be replaced by one with the same boundary and free interior. -/
theorem exists_free_pair {N : ℤ} (hN : 0 ≤ N) (X : SymPair (B.czIter k).inv N) :
    ∃ X' : SymPair (B.czIter k).inv N, X'.bd = X.bd ∧
      ∀ r, 0 ≤ r → r ≤ N + 1 → X'.pD.f r = 𝟙 _ :=
  Wall.exists_free_pair (hK.stablyFreeObjects hk) hN X

/-- A null-cobordant complex over `Kar (C_ℤ^{∘k} B)`, `k ≥ 1`, bounds a pair with free
interior. -/
theorem exists_free_nullCobordism {N : ℤ} (hN : 0 ≤ N) {P : SymPoincare (B.czIter k).inv N}
    (hP : NullCobordant P) :
    ∃ X : SymPair (B.czIter k).inv N, X.bd = P ∧ ∀ r, 0 ≤ r → r ≤ N + 1 → X.pD.f r = 𝟙 _ :=
  Wall.exists_free_nullCobordism (hK.stablyFreeObjects hk) hN hP

end NegKStablyFree

namespace NegK

variable {B : InvCat} (hK : NegK B) {k : ℕ} (hk : 1 ≤ k)
include hK hk

/-- **Symmetric Wall trick under `NegK`** (`N ≥ 1`): homotopy isometric to a free complex. -/
theorem exists_isometric_free {N : ℤ} (hN : 1 ≤ N) (P : SymPoincare (B.czIter k).inv N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, P.Isometric Q ∧ ∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _ :=
  hK.stablyFree.exists_isometric_free hk hN P

/-- **Symmetric Wall trick under `NegK`**: same `Lconc` class as a free complex. -/
theorem exists_cls_free {N : ℤ} (P : SymPoincare (B.czIter k).inv N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, (∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _) ∧
      Lconc.cls Q = Lconc.cls P :=
  hK.stablyFree.exists_cls_free hk P

/-- Under `NegK`, every element of `Lconc (C_ℤ^{∘k} B) N`, `k ≥ 1`, is the class of a free
complex. -/
theorem exists_free_of_lconc {N : ℤ} (x : Lconc (B.czIter k) N) :
    ∃ Q : SymPoincare (B.czIter k).inv N, (∀ r, 0 ≤ r → r ≤ N → Q.p.f r = 𝟙 _) ∧
      Lconc.cls Q = x :=
  hK.stablyFree.exists_free_of_lconc hk x

/-- **Relative symmetric Wall trick under `NegK`** (`N ≥ 0`): same boundary, free interior. -/
theorem exists_free_pair {N : ℤ} (hN : 0 ≤ N) (X : SymPair (B.czIter k).inv N) :
    ∃ X' : SymPair (B.czIter k).inv N, X'.bd = X.bd ∧
      ∀ r, 0 ≤ r → r ≤ N + 1 → X'.pD.f r = 𝟙 _ :=
  hK.stablyFree.exists_free_pair hk hN X

/-- Under `NegK`, a null-cobordant complex bounds a pair with free interior. -/
theorem exists_free_nullCobordism {N : ℤ} (hN : 0 ≤ N) {P : SymPoincare (B.czIter k).inv N}
    (hP : NullCobordant P) :
    ∃ X : SymPair (B.czIter k).inv N, X.bd = P ∧ ∀ r, 0 ≤ r → r ≤ N + 1 → X.pD.f r = 𝟙 _ :=
  hK.stablyFree.exists_free_nullCobordism hk hN hP

end NegK

end

end HSFormal.LTheory
