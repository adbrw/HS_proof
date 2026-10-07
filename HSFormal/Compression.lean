import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.CategoryTheory.Retract
import HSFormal.ControlledDuality

/-!
# Compression through the near part (manuscript §9)

The exact algebra of manuscript §9 (equations (9.1), (9.3)–(9.8), the inverse-defect,
chain-defect and adjoint formulas of Proposition 9.2), in an arbitrary preadditive category.

A near part of an object `Y` is a mathlib `Retract X Y`, i.e. `σ = R.i : X ⟶ Y` and
`π = R.r : Y ⟶ X` with `πσ = 1`; the far projection is `P = 1 - σπ`.  For a complex `D`,
degreewise near parts are `FarClosed` when `πdP = 0` (the far part is a subcomplex, as for the
carrier-defined `F_i` of l. 710) and `NearClosed` when `Pdσ = 0` (the dual condition, satisfied
by the dual near part `(π^*, σ^*)` of the shifted dual complex).

Composition is written diagrammatically: the manuscript's word `π a P d σ` is
`σ ≫ d ≫ P ≫ a ≫ π` here.  The shifted dual complex uses Ranicki's sign
`δ_r = (-1)^r d^*_{N-r+1}`, which is the convention under which the manuscript's formulas
`e^∨_r = (-1)^{r+1} e^*_{N-r+1}` and `K_r = (-1)^{r+1} T^*_{N-r-1}` hold.
-/

namespace HSFormal.Compression

noncomputable section

open CategoryTheory Category Limits Preadditive HomologicalComplex

variable {V : Type*} [Category V] [Preadditive V]

section Retract

/-- The far projection `P = 1 - σπ` of a near part (9.1). -/
def far {X Y : V} (R : Retract X Y) : Y ⟶ Y := 𝟙 Y - R.r ≫ R.i

/-- Compression `π f σ` through near parts (9.3). -/
def compress {X₁ Y₁ X₂ Y₂ : V} (R₁ : Retract X₁ Y₁) (R₂ : Retract X₂ Y₂) (f : Y₁ ⟶ Y₂) :
    X₁ ⟶ X₂ :=
  R₁.i ≫ f ≫ R₂.r

variable {X Y : V} (R : Retract X Y)

@[reassoc]
lemma r_i : R.r ≫ R.i = 𝟙 Y - far R := by simp [far]

@[reassoc (attr := simp)]
lemma far_r : far R ≫ R.r = 0 := by simp [far]

@[reassoc (attr := simp)]
lemma i_far : R.i ≫ far R = 0 := by simp [far]

@[reassoc (attr := simp)]
lemma far_far : far R ≫ far R = far R := by simp [far]

/-- The defect of compression on composites. -/
lemma compress_comp {X₁ Y₁ X₂ Y₂ X₃ Y₃ : V} (R₁ : Retract X₁ Y₁) (R₂ : Retract X₂ Y₂)
    (R₃ : Retract X₃ Y₃) (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    compress R₁ R₂ f ≫ compress R₂ R₃ g =
      compress R₁ R₃ (f ≫ g) - R₁.i ≫ f ≫ far R₂ ≫ g ≫ R₃.r := by
  simp [compress, far]

lemma compress_comp_eq_add {X₁ Y₁ X₂ Y₂ X₃ Y₃ : V} (R₁ : Retract X₁ Y₁) (R₂ : Retract X₂ Y₂)
    (R₃ : Retract X₃ Y₃) (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    compress R₁ R₃ (f ≫ g) =
      compress R₁ R₂ f ≫ compress R₂ R₃ g + R₁.i ≫ f ≫ far R₂ ≫ g ≫ R₃.r := by
  rw [compress_comp]; abel

/-- Equation (9.4): `α̂β̂ - (αβ)^ = -π α P β σ`. -/
theorem eq_9_4 {X₁ Y₁ X₂ Y₂ X₃ Y₃ : V} (R₁ : Retract X₁ Y₁) (R₂ : Retract X₂ Y₂)
    (R₃ : Retract X₃ Y₃) (β : Y₁ ⟶ Y₂) (α : Y₂ ⟶ Y₃) :
    compress R₁ R₂ β ≫ compress R₂ R₃ α - compress R₁ R₃ (β ≫ α) =
      -(R₁.i ≫ β ≫ far R₂ ≫ α ≫ R₃.r) := by
  rw [compress_comp]; abel

/-- Equation (9.7), first half: `φ̂b̂ = πφbσ - πφP^*bσ`, where `b̂ = σ^* b σ`, `φ̂ = π φ π^*`
and `R' = (π^*, σ^*)` is the near part on the dual side. -/
theorem eq_9_7_left {X' Y' : V} (R' : Retract X' Y') (b : Y ⟶ Y') (φ : Y' ⟶ Y) :
    compress R R' b ≫ compress R' R φ = compress R R (b ≫ φ) - R.i ≫ b ≫ far R' ≫ φ ≫ R.r :=
  compress_comp R R' R b φ

/-- Equation (9.7), second half: `b̂φ̂ = σ^*bφπ^* - σ^*bPφπ^*`. -/
theorem eq_9_7_right {X' Y' : V} (R' : Retract X' Y') (b : Y ⟶ Y') (φ : Y' ⟶ Y) :
    compress R' R φ ≫ compress R R' b = compress R' R' (φ ≫ b) - R'.i ≫ φ ≫ far R ≫ b ≫ R'.r :=
  compress_comp R' R R' φ b

omit [Preadditive V] in
/-- `A_1 = πσ = 1`. -/
@[simp]
theorem compress_id : compress R R (𝟙 Y) = 𝟙 X := by simp [compress]

omit [Preadditive V] in
/-- `A_1 = 1`, for any family `a` with `a 1 = 1`. -/
theorem compress_one {G : Type*} [One G] (a : G → (Y ⟶ Y)) (ha : a 1 = 𝟙 Y) :
    compress R R (a 1) = 𝟙 X := by
  rw [ha, compress_id]

/-- Equation (9.8): if `a z = z` then `A ẑ - ẑ = -π a P z`, where `ẑ = π z`. -/
theorem eq_9_8 {U : V} (a : Y ⟶ Y) (z : U ⟶ Y) (hz : z ≫ a = z) :
    (z ≫ R.r) ≫ compress R R a - z ≫ R.r = -(z ≫ far R ≫ a ≫ R.r) := by
  simp only [compress, far, assoc, sub_comp, comp_sub, id_comp, reassoc_of% hz]
  abel

end Retract

section Complex

variable {ι : Type*} {c : ComplexShape ι}

/-- Degreewise near parts `X k` of a complex `D`, with based sections `σ = (R k).i`. -/
abbrev NearPart (X : ι → V) (D : HomologicalComplex V c) := ∀ k, Retract (X k) (D.X k)

variable {X : ι → V} {D : HomologicalComplex V c} (R : NearPart X D)

/-- The compressed differential `d̂ = π d σ` (l. 719). -/
def hatD (i j : ι) : X i ⟶ X j := compress (R i) (R j) (D.d i j)

/-- Degreewise compression of a family of morphisms, e.g. a homotopy. -/
def compressFamily {X' : ι → V} {D' : HomologicalComplex V c} (R' : NearPart X' D')
    (H : ∀ i j, D.X i ⟶ D'.X j) (i j : ι) : X i ⟶ X' j :=
  compress (R i) (R' j) (H i j)

/-- `π d P = 0`: the far part is a subcomplex (l. 719). -/
def FarClosed : Prop := ∀ i j, far (R i) ≫ D.d i j ≫ (R j).r = 0

/-- `P d σ = 0`: the near part is a subcomplex. This is the dual of `FarClosed`. -/
def NearClosed : Prop := ∀ i j, (R i).i ≫ D.d i j ≫ far (R j) = 0

/-- The chain defect `e = dσ - σd̂` of the section. -/
def sectionDefect (i j : ι) : X i ⟶ D.X j := (R i).i ≫ D.d i j - hatD R i j ≫ (R j).i

/-- The chain defect `d̂π - πd` of the retraction; on the dual side this is
`e^∨ = δ̂σ^* - σ^*δ`. -/
def retractionDefect (i j : ι) : D.X i ⟶ X j := (R i).r ≫ hatD R i j - D.d i j ≫ (R j).r

/-- `e = P d σ`. -/
theorem sectionDefect_eq (i j : ι) :
    sectionDefect R i j = (R i).i ≫ D.d i j ≫ far (R j) := by
  simp [sectionDefect, hatD, compress, far]

/-- `e^∨` factors through the far projection: `e^∨ = -σ^* δ P^*`. -/
theorem retractionDefect_eq (i j : ι) :
    retractionDefect R i j = -(far (R i) ≫ D.d i j ≫ (R j).r) := by
  simp [retractionDefect, hatD, compress, far]

theorem farClosed_iff : FarClosed R ↔ ∀ i j, retractionDefect R i j = 0 := by
  simp [FarClosed, retractionDefect_eq]

theorem nearClosed_iff : NearClosed R ↔ ∀ i j, sectionDefect R i j = 0 := by
  simp [NearClosed, sectionDefect_eq]

/-- `πdP = 0` holds when `P` factors through a subcomplex killed by `π`, as for the carrier-defined
far subcomplex `F_i` of l. 710. -/
theorem farClosed_of_subcomplex {F : HomologicalComplex V c} (j : F ⟶ D)
    (q : ∀ k, D.X k ⟶ F.X k) (hq : ∀ k, far (R k) = q k ≫ j.f k)
    (hj : ∀ k, j.f k ≫ (R k).r = 0) : FarClosed R := by
  intro k l
  rw [hq, assoc, j.comm_assoc, hj, comp_zero, comp_zero]

/-- If `π` is a chain map to some complex, then `πdP = 0`. -/
theorem farClosed_of_hom {C : HomologicalComplex V c} (R : NearPart C.X D) (p : D ⟶ C)
    (hp : ∀ k, (R k).r = p.f k) : FarClosed R := by
  intro k l
  have hk : (R k).i ≫ p.f k = 𝟙 _ := by rw [← hp]; exact (R k).retract
  rw [far, hp, hp, sub_comp, id_comp, assoc, ← p.comm, reassoc_of% hk, sub_self]

/-- If `π` is a chain map to some complex `C`, its differential is the compressed one. -/
theorem hatD_eq_of_hom {C : HomologicalComplex V c} (R : NearPart C.X D) (p : D ⟶ C)
    (hp : ∀ k, (R k).r = p.f k) (i j : ι) : hatD R i j = C.d i j := by
  have hi : (R i).i ≫ p.f i = 𝟙 _ := by rw [← hp]; exact (R i).retract
  rw [hatD, compress, hp, ← p.comm, reassoc_of% hi]

/-- If `σ` is a chain map from some complex, then `Pdσ = 0`. -/
theorem nearClosed_of_hom {C : HomologicalComplex V c} (R : NearPart C.X D) (s : C ⟶ D)
    (hs : ∀ k, (R k).i = s.f k) : NearClosed R := by
  intro k l
  have hl : s.f l ≫ (R l).r = 𝟙 _ := by rw [← hs]; exact (R l).retract
  simp only [far, hs, comp_sub, comp_id, Hom.comm_assoc, reassoc_of% hl, Hom.comm, sub_self]

theorem hatD_comp_hatD (h : FarClosed R ∨ NearClosed R) (i j k : ι) :
    hatD R i j ≫ hatD R j k = 0 := by
  rw [hatD, hatD, compress_comp, D.d_comp_d]
  rcases h with h | h
  · simp [h j k, compress]
  · simp [reassoc_of% (h i j), compress]

/-- The compressed complex `(C, d̂)`; `d̂² = 0` under either closure condition. -/
@[simps]
def compressed (h : FarClosed R ∨ NearClosed R) : HomologicalComplex V c where
  X := X
  d := hatD R
  shape i j hij := by rw [hatD, compress, D.shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := hatD_comp_hatD R h i j k

/-- The quotient map `π` is an exact chain map. -/
@[simps]
def quotientMap (h : FarClosed R) : D ⟶ compressed R (.inl h) where
  f k := (R k).r
  comm' i j _ := by
    have := (farClosed_iff R).1 h i j
    rw [retractionDefect, sub_eq_zero] at this
    exact this

/-- For a near-closed near part, the section `σ` is an exact chain map. -/
@[simps]
def sectionMap (h : NearClosed R) : compressed R (.inr h) ⟶ D where
  f k := (R k).i
  comm' i j _ := by
    have := (nearClosed_iff R).1 h i j
    rw [sectionDefect, sub_eq_zero] at this
    exact this

variable {X' : ι → V} {D' : HomologicalComplex V c} (R' : NearPart X' D')

/-- A chain map from a near-closed to a far-closed complex compresses to an exact chain map
(l. 769: `φ̂ = πφπ^*` is a chain map because `π` and `π^*` are). -/
def compressHom (h' : NearClosed R') (h : FarClosed R) (φ : D' ⟶ D) :
    compressed R' (.inr h') ⟶ compressed R (.inl h) :=
  sectionMap R' h' ≫ φ ≫ quotientMap R h

@[simp]
theorem compressHom_f (h' : NearClosed R') (h : FarClosed R) (φ : D' ⟶ D) (k : ι) :
    (compressHom R R' h' h φ).f k = compress (R' k) (R k) (φ.f k) :=
  rfl

/-- The chain defect of a compressed chain map: `d̂'f̂ - f̂d̂ = e'^∨ f σ + π' f e`.
For `f = b` this is `δ̂b̂ - b̂d̂ = e^∨bσ + σ^*be`. -/
theorem compress_comm (f : D ⟶ D') (i j : ι) :
    compress (R i) (R' i) (f.f i) ≫ hatD R' i j - hatD R i j ≫ compress (R j) (R' j) (f.f j) =
      (R i).i ≫ f.f i ≫ retractionDefect R' i j + sectionDefect R i j ≫ f.f j ≫ (R' j).r := by
  simp only [compress, retractionDefect, sectionDefect, hatD, comp_sub, sub_comp, assoc]
  rw [← f.comm_assoc]
  abel

/-- Equation (9.5): `d̂â - âd̂ = π a P d σ` for a chain map `a`. -/
theorem eq_9_5 (h : FarClosed R) (a : D ⟶ D) (i j : ι) :
    compress (R i) (R i) (a.f i) ≫ hatD R i j - hatD R i j ≫ compress (R j) (R j) (a.f j) =
      (R i).i ≫ D.d i j ≫ far (R j) ≫ a.f j ≫ (R j).r := by
  rw [compress_comm, (farClosed_iff R).1 h, sectionDefect_eq]
  simp

/-- The chain defect of `b̂ = σ^* b σ`: `δ̂b̂ - b̂d̂ = e^∨ b σ + σ^* b e`. -/
theorem bHat_chainDefect (b : D ⟶ D') (i j : ι) :
    compress (R i) (R' i) (b.f i) ≫ hatD R' i j - hatD R i j ≫ compress (R j) (R' j) (b.f j) =
      (R i).i ≫ b.f i ≫ retractionDefect R' i j + sectionDefect R i j ≫ b.f j ≫ (R' j).r :=
  compress_comm R R' b i j

/-- Compression of a homotopy relation `f - g = dH + Hd'` at the indices `n = next i`,
`p = prev i`: `f̂ - ĝ - (d̂Ĥ + Ĥd̂') = π' H e - e'^∨ H σ`. -/
theorem compress_homotopy_at (f g : D ⟶ D') (H : ∀ i j, D.X i ⟶ D'.X j) (i n p : ι)
    (hH : f.f i = D.d i n ≫ H n i + H i p ≫ D'.d p i + g.f i) :
    compress (R i) (R' i) (f.f i) - compress (R i) (R' i) (g.f i) -
        (hatD R i n ≫ compressFamily R R' H n i + compressFamily R R' H i p ≫ hatD R' p i) =
      sectionDefect R i n ≫ H n i ≫ (R' i).r - (R i).i ≫ H i p ≫ retractionDefect R' p i := by
  simp only [compress, compressFamily, retractionDefect, sectionDefect, hatD, hH, comp_sub,
    sub_comp, comp_add, add_comp, assoc]
  abel

/-- `d̂Ĥ + Ĥd̂'` at degree `i`, the null-homotopic term of the compressed family `Ĥ = πHσ`;
in the compressed complexes it is `dNext i Ĥ + prevD i Ĥ` (`hatDH_eq`). -/
def hatDH (H : ∀ i j, D.X i ⟶ D'.X j) (i : ι) : X i ⟶ X' i :=
  hatD R i (c.next i) ≫ compressFamily R R' H (c.next i) i +
    compressFamily R R' H i (c.prev i) ≫ hatD R' (c.prev i) i

theorem hatDH_eq (h : FarClosed R ∨ NearClosed R) (h' : FarClosed R' ∨ NearClosed R')
    (H : ∀ i j, D.X i ⟶ D'.X j) (i : ι) :
    (hatDH R R' H i : (compressed R h).X i ⟶ (compressed R' h').X i) =
      dNext (C := compressed R h) (D := compressed R' h') i (compressFamily R R' H) +
        prevD (C := compressed R h) (D := compressed R' h') i (compressFamily R R' H) :=
  rfl

/-- Compression of a chain homotopy `f - g = dH + Hd'`:
`f̂ - ĝ - (d̂Ĥ + Ĥd̂') = π' H e - e'^∨ H σ`. -/
theorem compress_homotopy {f g : D ⟶ D'} (H : Homotopy f g) (i : ι) :
    compress (R i) (R' i) (f.f i) - compress (R i) (R' i) (g.f i) - hatDH R R' H.hom i =
      sectionDefect R i (c.next i) ≫ H.hom (c.next i) i ≫ (R' i).r -
        (R i).i ≫ H.hom i (c.prev i) ≫ retractionDefect R' (c.prev i) i :=
  compress_homotopy_at R R' f g H.hom i (c.next i) (c.prev i) (H.comm i)

/-- Equation (9.6): from `a₁a₂ - a₃ = dB + Bd` (8.5) (diagrammatic `a₁ ≫ a₂`; in the paper
`a₁ = a_h`, `a₂ = a_g`, `a₃ = a_{gh}`),
`A_gA_h - A_{gh} - d̂B̂ - B̂d̂ = -π a_g P a_h σ + π B P d σ`. -/
theorem eq_9_6 (h : FarClosed R) {a₁ a₂ a₃ : D ⟶ D} (B : Homotopy (a₁ ≫ a₂) a₃) (i : ι) :
    compress (R i) (R i) (a₁.f i) ≫ compress (R i) (R i) (a₂.f i) - compress (R i) (R i) (a₃.f i) -
      hatDH R R B.hom i =
      -((R i).i ≫ a₁.f i ≫ far (R i) ≫ a₂.f i ≫ (R i).r) +
        (R i).i ≫ D.d i (c.next i) ≫ far (R (c.next i)) ≫ B.hom (c.next i) i ≫ (R i).r := by
  have key := compress_homotopy R R B i
  rw [comp_f, compress_comp_eq_add (R i) (R i) (R i), (farClosed_iff R).1 h, sectionDefect_eq,
    comp_zero, comp_zero, sub_zero] at key
  rw [← sub_eq_zero, ← sub_eq_zero.mpr key]
  simp only [assoc]
  abel

/-- The first inverse-defect formula of Proposition 9.2: from `φb - 1 = dH + Hd`,
`φ̂b̂ - 1 = d̂(πHσ) + (πHσ)d̂ + πHe - πφP^*bσ`. -/
theorem inverse_defect_left (h : FarClosed R) {b : D ⟶ D'} {φ : D' ⟶ D}
    (H : Homotopy (b ≫ φ) (𝟙 D)) (i : ι) :
    compress (R i) (R' i) (b.f i) ≫ compress (R' i) (R i) (φ.f i) - 𝟙 (X i) =
      hatDH R R H.hom i +
        sectionDefect R i (c.next i) ≫ H.hom (c.next i) i ≫ (R i).r -
        (R i).i ≫ b.f i ≫ far (R' i) ≫ φ.f i ≫ (R i).r := by
  have key := compress_homotopy R R H i
  rw [comp_f, id_f, compress_comp_eq_add (R i) (R' i) (R i), compress_id,
    (farClosed_iff R).1 h, comp_zero, comp_zero, sub_zero] at key
  rw [← sub_eq_zero, ← sub_eq_zero.mpr key]
  abel

/-- The second inverse-defect formula of Proposition 9.2: from `bφ - 1 = δH' + H'δ`,
`b̂φ̂ - 1 = δ̂(σ^*H'π^*) + (σ^*H'π^*)δ̂ - e^∨H'π^* - σ^*bPφπ^*`. -/
theorem inverse_defect_right (h' : NearClosed R') {b : D ⟶ D'} {φ : D' ⟶ D}
    (H' : Homotopy (φ ≫ b) (𝟙 D')) (i : ι) :
    compress (R' i) (R i) (φ.f i) ≫ compress (R i) (R' i) (b.f i) - 𝟙 (X' i) =
      hatDH R' R' H'.hom i -
        (R' i).i ≫ H'.hom i (c.prev i) ≫ retractionDefect R' (c.prev i) i -
        (R' i).i ≫ φ.f i ≫ far (R i) ≫ b.f i ≫ (R' i).r := by
  have key := compress_homotopy R' R' H' i
  rw [comp_f, id_f, compress_comp_eq_add (R' i) (R i) (R' i), compress_id,
    (nearClosed_iff R').1 h', zero_comp, zero_sub] at key
  rw [← sub_eq_zero, ← sub_eq_zero.mpr key]
  abel

/-- The adjoint formula of Proposition 9.2: from `aφ - φa' = dV + Vδ`,
`A φ̂ - φ̂ A' - d̂V̂ - V̂δ̂ = -π a P φ π^* + π φ P^* a' π^*` with `V̂ = πVπ^*`; in the paper
`a = a_g` and `a' = a_{g⁻¹}^*`, so that `A' = A_{g⁻¹}^*` (see `adjoint_formula`). -/
theorem adjoint_defect (h : FarClosed R) (h' : NearClosed R') {a : D ⟶ D} {a' : D' ⟶ D'}
    {φ : D' ⟶ D} (W : Homotopy (φ ≫ a) (a' ≫ φ)) (i : ι) :
    compress (R' i) (R i) (φ.f i) ≫ compress (R i) (R i) (a.f i) -
        compress (R' i) (R' i) (a'.f i) ≫ compress (R' i) (R i) (φ.f i) - hatDH R' R W.hom i =
      -((R' i).i ≫ φ.f i ≫ far (R i) ≫ a.f i ≫ (R i).r) +
        (R' i).i ≫ a'.f i ≫ far (R' i) ≫ φ.f i ≫ (R i).r := by
  have key := compress_homotopy R' R W i
  rw [comp_f, comp_f, compress_comp_eq_add (R' i) (R i) (R i),
    compress_comp_eq_add (R' i) (R' i) (R i), (nearClosed_iff R').1 h', (farClosed_iff R).1 h,
    zero_comp, comp_zero, comp_zero, sub_zero] at key
  rw [← sub_eq_zero, ← sub_eq_zero.mpr key]
  abel

end Complex

/-- A strict additive involution fixing objects, as the transpose of based matrices
(manuscript §2: "the dual uses the same labelled basis and the transpose matrix"). -/
structure StrictInvolution (V : Type*) [Category V] [Preadditive V] where
  /-- The dual `f^*` of a morphism. -/
  star : ∀ {X Y : V}, (X ⟶ Y) → (Y ⟶ X)
  star_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z), star (f ≫ g) = star g ≫ star f
  star_id : ∀ X : V, star (𝟙 X) = 𝟙 X
  star_add : ∀ {X Y : V} (f g : X ⟶ Y), star (f + g) = star f + star g
  star_star : ∀ {X Y : V} (f : X ⟶ Y), star (star f) = f

namespace StrictInvolution

variable (J : StrictInvolution V)

/-- `star` as an additive map. -/
def starHom (X Y : V) : (X ⟶ Y) →+ (Y ⟶ X) := AddMonoidHom.mk' J.star J.star_add

@[simp]
lemma star_zero {X Y : V} : J.star (0 : X ⟶ Y) = 0 := map_zero (J.starHom X Y)

@[simp]
lemma star_neg {X Y : V} (f : X ⟶ Y) : J.star (-f) = -J.star f := map_neg (J.starHom X Y) f

@[simp]
lemma star_sub {X Y : V} (f g : X ⟶ Y) : J.star (f - g) = J.star f - J.star g :=
  map_sub (J.starHom X Y) f g

@[simp]
lemma star_units_smul {X Y : V} (u : ℤˣ) (f : X ⟶ Y) : J.star (u • f) = u • J.star f := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (J.starHom X Y) (u : ℤ) f

attribute [simp] star_id star_star

end StrictInvolution

section Duality

variable (J : StrictInvolution V)

/-- The dual near part `(π^*, σ^*)` of a near part `(σ, π)`. -/
@[simps]
def starRetract {X Y : V} (R : Retract X Y) : Retract X Y where
  i := J.star R.r
  r := J.star R.i
  retract := by rw [← J.star_comp, R.retract, J.star_id]

/-- The dual far projection is `P^*`. -/
@[simp]
lemma far_starRetract {X Y : V} (R : Retract X Y) : far (starRetract J R) = J.star (far R) := by
  simp [far, J.star_comp]

/-- Compression commutes with duality: `(π f σ)^* = σ^* f^* π^*`. -/
lemma compress_star {X₁ Y₁ X₂ Y₂ : V} (R₁ : Retract X₁ Y₁) (R₂ : Retract X₂ Y₂) (f : Y₁ ⟶ Y₂) :
    compress (starRetract J R₂) (starRetract J R₁) (J.star f) = J.star (compress R₁ R₂ f) := by
  simp [compress, J.star_comp]

variable (N : ℤ)

/-- The shifted dual complex `D^{N-*}`: `(D^{N-*})_r = D_{N-r}`, with Ranicki's differential
`δ_r = (-1)^r d^*_{N-r+1}`. -/
@[simps, reducible]
def dualComplex (D : ChainComplex V ℤ) : ChainComplex V ℤ where
  X r := D.X (N - r)
  d r r' := r.negOnePow • J.star (D.d (N - r') (N - r))
  shape r r' hr := by
    rw [D.shape, J.star_zero, smul_zero]
    simp only [ComplexShape.down_Rel] at hr ⊢
    omega
  d_comp_d' r r' r'' _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, ← J.star_comp, D.d_comp_d, J.star_zero,
      smul_zero, smul_zero]

/-- The dual chain map `f^{N-*}`, `(f^{N-*})_r = f^*_{N-r}` (no sign). -/
@[simps]
def dualHom {D D' : ChainComplex V ℤ} (f : D ⟶ D') : dualComplex J N D' ⟶ dualComplex J N D where
  f r := J.star (f.f (N - r))
  comm' r r' _ := by
    simp only [dualComplex_d, Linear.comp_units_smul, Linear.units_smul_comp, ← J.star_comp,
      Hom.comm]

@[simp]
lemma dualHom_comp {D D' D'' : ChainComplex V ℤ} (f : D ⟶ D') (g : D' ⟶ D'') :
    dualHom J N (f ≫ g) = dualHom J N g ≫ dualHom J N f := by
  ext r; simp [J.star_comp]

@[simp]
lemma dualHom_id (D : ChainComplex V ℤ) : dualHom J N (𝟙 D) = 𝟙 _ := by
  ext r; simp

/-- The dual homotopy `K_r = (-1)^{r+1} T^*_{N-r-1}` (l. 699): if `f - g = dT + Td` then
`f^{N-*} - g^{N-*} = δK + Kδ`. -/
@[simps]
def dualHomotopy {D D' : ChainComplex V ℤ} {f g : D ⟶ D'} (T : Homotopy f g) :
    Homotopy (dualHom J N f) (dualHom J N g) where
  hom r r' := (r + 1).negOnePow • J.star (T.hom (N - r') (N - r))
  zero r r' hr := by
    rw [T.zero, J.star_zero, smul_zero]
    simp only [ComplexShape.down_Rel] at hr ⊢
    omega
  comm r := by
    have hT := T.comm (N - r)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (N - r) (N - (r + 1)) by simp; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (N - (r - 1)) (N - r) by simp; omega)] at hT
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    simp only [dualHom_f, dualComplex_d, hT, J.star_add, Linear.units_smul_comp,
      Linear.comp_units_smul, ← J.star_comp, smul_smul, sub_add_cancel, Int.units_mul_self,
      one_smul]
    abel

/-- §8, l. 700–702: with `K` the dual of `T : ba ≃ 1` and `U : aφa^* ≃ φ` (8.6), the map
`V = -aφK + Ub^*` satisfies `dV + Vδ = aφ - φb^*`. -/
def adjointHomotopy {D : ChainComplex V ℤ} {a b : D ⟶ D} {φ : dualComplex J N D ⟶ D}
    (T : Homotopy (a ≫ b) (𝟙 D)) (U : Homotopy (dualHom J N a ≫ φ ≫ a) φ) :
    Homotopy (φ ≫ a) (dualHom J N b ≫ φ) :=
  (Homotopy.ofEq (by simp)).trans <| ((dualHomotopy J N T).compRight (φ ≫ a)).symm.trans <|
    (Homotopy.ofEq (by simp)).trans (U.compLeft (dualHom J N b))

lemma adjointHomotopy_hom {D : ChainComplex V ℤ} {a b : D ⟶ D} {φ : dualComplex J N D ⟶ D}
    (T : Homotopy (a ≫ b) (𝟙 D)) (U : Homotopy (dualHom J N a ≫ φ ≫ a) φ) (r r' : ℤ) :
    (adjointHomotopy J N T U).hom r r' =
      -((dualHomotopy J N T).hom r r' ≫ φ.f r' ≫ a.f r') + (dualHom J N b).f r ≫ U.hom r r' := by
  simp [adjointHomotopy, Homotopy.ofEq, Homotopy.trans, Homotopy.symm, Homotopy.compRight,
    Homotopy.compLeft]

variable {X : ℤ → V} {D : ChainComplex V ℤ} (R : NearPart X D)

/-- The near part `(π^*, σ^*)` of the shifted dual complex. -/
def dualNearPart : NearPart (fun r ↦ X (N - r)) (dualComplex J N D) :=
  fun r ↦ starRetract J (R (N - r))

@[simp]
lemma dualNearPart_i (r : ℤ) : (dualNearPart J N R r).i = J.star (R (N - r)).r := rfl

@[simp]
lemma dualNearPart_r (r : ℤ) : (dualNearPart J N R r).r = J.star (R (N - r)).i := rfl

/-- The dual near part of a far-closed near part is near-closed: `π^*` is a chain map. -/
theorem nearClosed_dual (h : FarClosed R) : NearClosed (dualNearPart J N R) := by
  intro r r'
  simp only [dualNearPart, far_starRetract, starRetract_i, dualComplex_d, Linear.units_smul_comp,
    Linear.comp_units_smul, ← J.star_comp, assoc]
  rw [h (N - r') (N - r), J.star_zero, smul_zero]

theorem farClosed_dual (h : NearClosed R) : FarClosed (dualNearPart J N R) := by
  intro r r'
  simp only [dualNearPart, far_starRetract, starRetract_r, dualComplex_d, Linear.units_smul_comp,
    Linear.comp_units_smul, ← J.star_comp, assoc]
  rw [h (N - r') (N - r), J.star_zero, smul_zero]

/-- `δ̂ = (d̂)^{N-*}`: the compressed dual differential is the dual of the compressed one. -/
theorem hatD_dual (r r' : ℤ) :
    hatD (dualNearPart J N R) r r' = r.negOnePow • J.star (hatD R (N - r') (N - r)) := by
  simp only [hatD, dualNearPart, ← compress_star, dualComplex_d]
  simp [compress, Linear.units_smul_comp, Linear.comp_units_smul]

/-- Compressing the dual complex gives the dual of the compressed complex. -/
theorem compressed_dual (h : FarClosed R) :
    compressed (dualNearPart J N R) (.inr (nearClosed_dual J N R h)) =
      dualComplex J N (compressed R (.inl h)) :=
  HomologicalComplex.ext rfl fun r r' _ ↦
    (Category.comp_id _).trans ((hatD_dual J N R r r').trans (Category.id_comp _).symm)

/-- `e^∨_r = (-1)^{r+1} e^*_{N-r+1}`: the chain defect `e^∨ = δ̂σ^* - σ^*δ` of `σ^*` is the
signed dual of the chain defect `e = dσ - σd̂` of `σ`. -/
theorem retractionDefect_dual (r r' : ℤ) :
    retractionDefect (dualNearPart J N R) r r' =
      (r + 1).negOnePow • J.star (sectionDefect R (N - r') (N - r)) := by
  rw [retractionDefect, hatD_dual, sectionDefect, J.star_sub, Int.negOnePow_succ, Units.neg_smul,
    smul_sub]
  simp only [dualNearPart_r, dualComplex_d, Linear.comp_units_smul, Linear.units_smul_comp,
    ← J.star_comp]
  abel

theorem sectionDefect_dual (r r' : ℤ) :
    sectionDefect (dualNearPart J N R) r r' =
      (r + 1).negOnePow • J.star (retractionDefect R (N - r') (N - r)) := by
  rw [sectionDefect, hatD_dual, retractionDefect, J.star_sub, Int.negOnePow_succ, Units.neg_smul,
    smul_sub]
  simp only [dualNearPart_i, dualComplex_d, Linear.comp_units_smul, Linear.units_smul_comp,
    ← J.star_comp]
  abel

/-- `A^*`: compressing the dual of a chain map is dualizing its compression. -/
theorem compress_dualHom {X' : ℤ → V} {D' : ChainComplex V ℤ} (R' : NearPart X' D') (f : D ⟶ D')
    (r : ℤ) :
    compress (dualNearPart J N R' r) (dualNearPart J N R r) ((dualHom J N f).f r) =
      J.star (compress (R (N - r)) (R' (N - r)) (f.f (N - r))) :=
  compress_star J _ _ _

/-- The adjoint formula of Proposition 9.2 with the paper's duality: if `aφ - φb^* = dV + Vδ`
(`a = a_g`, `b = a_{g⁻¹}`), then
`A_gφ̂ - φ̂A_{g⁻¹}^* - d̂V̂ - V̂δ̂ = -π a P φ π^* + π φ P^* b^* π^*`,
with `φ̂ = πφπ^*` and `V̂ = πVπ^*`. -/
theorem adjoint_formula (h : FarClosed R) {a b : D ⟶ D} {φ : dualComplex J N D ⟶ D}
    (W : Homotopy (φ ≫ a) (dualHom J N b ≫ φ)) (r : ℤ) :
    compress (dualNearPart J N R r) (R r) (φ.f r) ≫ compress (R r) (R r) (a.f r) -
        J.star (compress (R (N - r)) (R (N - r)) (b.f (N - r))) ≫
          compress (dualNearPart J N R r) (R r) (φ.f r) -
        hatDH (dualNearPart J N R) R W.hom r =
      -(J.star (R (N - r)).r ≫ φ.f r ≫ far (R r) ≫ a.f r ≫ (R r).r) +
        J.star (R (N - r)).r ≫ J.star (b.f (N - r)) ≫ J.star (far (R (N - r))) ≫ φ.f r ≫
          (R r).r := by
  rw [← compress_dualHom J N R R b r, adjoint_defect R (dualNearPart J N R) h
    (nearClosed_dual J N R h) W r]
  simp [dualNearPart]

/-- `φ̂ = πφπ^* : C^{N-*} ⟶ C` is an exact chain map (l. 769). -/
@[simps]
def hatPhi (h : FarClosed R) (φ : dualComplex J N D ⟶ D) :
    dualComplex J N (compressed R (.inl h)) ⟶ compressed R (.inl h) where
  f r := compress (dualNearPart J N R r) (R r) (φ.f r)
  comm' r r' _ := by
    have := (compressHom R (dualNearPart J N R) (nearClosed_dual J N R h) h φ).comm r r'
    rw [compressHom_f, compressHom_f] at this
    exact this.trans (by rw [compressed_d, hatD_dual]; rfl)

/-- Ranicki's transposition `(Tφ)_r = (-1)^{r(N-r)} φ_{N-r}^*` of a family
`φ_r : Y_{N-r} ⟶ Y_r`; `φ` is strictly symmetric when `Tφ = φ`. -/
def transposeFamily (Y : ℤ → V) (φ : ∀ r, Y (N - r) ⟶ Y r) (r : ℤ) : Y (N - r) ⟶ Y r :=
  (r * (N - r)).negOnePow • (J.star (φ (N - r)) ≫ eqToHom (congrArg Y (sub_sub_cancel N r)))

lemma retract_r_eqToHom {ι : Type*} {c : ComplexShape ι} {X : ι → V}
    {D : HomologicalComplex V c} (R : NearPart X D) {k k' : ι} (h : k = k') :
    (R k).r ≫ eqToHom (congrArg X h) = eqToHom (congrArg D.X h) ≫ (R k').r := by
  subst h; simp

/-- l. 769: `φ̂ = πφπ^*` is strictly symmetric when `φ` is. -/
theorem compress_symmetric (φ : ∀ r, D.X (N - r) ⟶ D.X r)
    (hφ : ∀ r, φ r = transposeFamily J N D.X φ r) (r : ℤ) :
    compress (dualNearPart J N R r) (R r) (φ r) =
      transposeFamily J N X (fun s ↦ compress (dualNearPart J N R s) (R s) (φ s)) r := by
  rw [transposeFamily, hφ r, transposeFamily]
  simp only [compress, dualNearPart_i, J.star_comp, J.star_star, assoc, Linear.comp_units_smul,
    Linear.units_smul_comp]
  rw [retract_r_eqToHom R (sub_sub_cancel N r)]

end Duality

section Controlled

open ControlledObject

variable (X : Type*) [PseudoMetricSpace X]

/-- Transpose on the scalar controlled category. -/
def controlledInvolution : StrictInvolution (ControlledObject X) where
  star := controlledTranspose
  star_comp := controlledTranspose_comp
  star_id := controlledTranspose_id
  star_add := controlledTranspose_add
  star_star := controlledTranspose_transpose

/-- Transpose on the tail (eventual-equality) quotient. -/
def tailInvolution : StrictInvolution (TailCategory X) where
  star := tailTranspose
  star_comp := tailTranspose_comp
  star_id := tailTranspose_id
  star_add := tailTranspose_add
  star_star := tailTranspose_transpose

end Controlled

end

end HSFormal.Compression
