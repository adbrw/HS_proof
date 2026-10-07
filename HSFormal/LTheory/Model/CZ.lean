import HSFormal.LTheory.KaroubiFiltration
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval

/-!
# The bounded category `C_ℤ(A)` (lower L-theory model, module 1)

For an `InvCat` `A`, the bounded category `C_ℤ(A)` of [PW85] ([Ran92, §§4, 15]):

* objects `X = (X_v)_{v ∈ ℤ}` are arbitrary `ℤ`-indexed families of objects of `A` (every point of
  `ℤ` carries one object, so local finiteness is automatic);
* morphisms `f : X ⟶ Y` are matrices `f w v : X_v ⟶ Y_w` (target index first) of bounded
  propagation: `∃ b, |w - v| > b → f w v = 0` (`PropLE`);
* composition is the matrix product `(f ≫ g) u v = ∑ᶠ w, f w v ≫ g u w`, a finite sum since `f`
  is bounded; `matComp_eq_sum_left`/`matComp_eq_sum_right` evaluate it over explicit windows;
* biproducts and unitary bicones are pointwise (`biconeOf`, `unitaryBicone`); the involution is
  the entrywise transpose `(f^*) v w = (f w v)^*`.

`InvCat.cz A` packages this as an `InvCat`.  The functoriality `CZ.map`, its laws, the iterates
`InvCat.czIter` and `CZ.mapIter` are in `Model/CZFunctor.lean`.

The API is stated for `CZ.Obj A`; `InvCat.cz` is reducible, so it applies verbatim to `A.cz`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

namespace CZ

variable (A : InvCat)

/-- An object of `C_ℤ(A)`: an object of `A` at every `v : ℤ`. -/
@[ext]
structure Obj where
  /-- The object at position `v`. -/
  obj : ℤ → A

variable {A}

/-- Raw matrices `f w v : X v ⟶ Y w` (target index first). -/
abbrev Mat (X Y : Obj A) : Type := ∀ w v : ℤ, X.obj v ⟶ Y.obj w

/-- `f` has propagation at most `b`. -/
def PropLE {X Y : Obj A} (f : Mat X Y) (b : ℕ) : Prop :=
  ∀ w v, (b : ℤ) < |w - v| → f w v = 0

/-! ### Windows and propagation bounds -/

/-- The window `[v - b, v + b]`. -/
def window (v : ℤ) (b : ℕ) : Finset ℤ := Finset.Icc (v - b) (v + b)

lemma lt_abs_of_notMem_window {v w : ℤ} {b : ℕ} (h : w ∉ window v b) : (b : ℤ) < |w - v| := by
  simp only [window, Finset.mem_Icc, not_and_or, not_le] at h
  rw [lt_abs]; omega

lemma lt_abs_of_notMem_window' {v w : ℤ} {b : ℕ} (h : w ∉ window v b) : (b : ℤ) < |v - w| := by
  rw [abs_sub_comm]; exact lt_abs_of_notMem_window h

variable {X Y Z T : Obj A}

namespace PropLE

variable {f g : Mat X Y} {b c : ℕ}

lemma mono (hf : PropLE f b) (h : b ≤ c) : PropLE f c := fun w v hwv ↦
  hf w v (lt_of_le_of_lt (by exact_mod_cast h) hwv)

lemma zero (b : ℕ) : PropLE (0 : Mat X Y) b := fun _ _ _ ↦ rfl

lemma add (hf : PropLE f b) (hg : PropLE g c) : PropLE (f + g) (max b c) := fun w v h ↦ by
  change f w v + g w v = 0
  rw [(hf.mono (le_max_left b c)) w v h, (hg.mono (le_max_right b c)) w v h, add_zero]

lemma smul (r : ℚ) (hf : PropLE f b) : PropLE (r • f) b := fun w v h ↦ by
  change r • f w v = 0
  rw [hf w v h, smul_zero]

/-- Entries outside the window of a column vanish. -/
lemma eq_zero_col (hf : PropLE f b) {w v : ℤ} (h : w ∉ window v b) : f w v = 0 :=
  hf w v (lt_abs_of_notMem_window h)

/-- Entries outside the window of a row vanish. -/
lemma eq_zero_row (hf : PropLE f b) {w v : ℤ} (h : v ∉ window w b) : f w v = 0 :=
  hf w v (lt_abs_of_notMem_window' h)

end PropLE

/-- Bounded matrices form a `ℚ`-submodule. -/
def boundedSubmodule (X Y : Obj A) : Submodule ℚ (Mat X Y) where
  carrier := {f | ∃ b, PropLE f b}
  zero_mem' := ⟨0, PropLE.zero 0⟩
  add_mem' := fun ⟨_, hf⟩ ⟨_, hg⟩ ↦ ⟨_, hf.add hg⟩
  smul_mem' r _ := fun ⟨_, hf⟩ ↦ ⟨_, hf.smul r⟩

lemma mem_boundedSubmodule {f : Mat X Y} : f ∈ boundedSubmodule X Y ↔ ∃ b, PropLE f b :=
  Iff.rfl

/-! ### Matrix product -/

/-- Matrix product `(f ≫ g) u v = ∑ᶠ w, f w v ≫ g u w`. -/
def matComp (f : Mat X Y) (g : Mat Y Z) : Mat X Z :=
  fun u v ↦ ∑ᶠ w, f w v ≫ g u w

/-- The product over any window containing all nonzero terms. -/
lemma matComp_eq_sum {f : Mat X Y} {g : Mat Y Z} {u v : ℤ} (s : Finset ℤ)
    (h : ∀ w ∉ s, f w v ≫ g u w = 0) : matComp f g u v = ∑ w ∈ s, f w v ≫ g u w :=
  finsum_eq_sum_of_support_subset _ fun w hw ↦ by
    by_contra hs
    exact (Function.mem_support.mp hw) (h w hs)

/-- The product, using the bound of the left factor (window around the column). -/
lemma matComp_eq_sum_left {f : Mat X Y} {b : ℕ} (hf : PropLE f b) (g : Mat Y Z) (u v : ℤ) :
    matComp f g u v = ∑ w ∈ window v b, f w v ≫ g u w :=
  matComp_eq_sum _ fun _ hw ↦ by rw [hf.eq_zero_col hw, zero_comp]

/-- The product, using the bound of the right factor (window around the row). -/
lemma matComp_eq_sum_right (f : Mat X Y) {g : Mat Y Z} {b : ℕ} (hg : PropLE g b) (u v : ℤ) :
    matComp f g u v = ∑ w ∈ window u b, f w v ≫ g u w :=
  matComp_eq_sum _ fun _ hw ↦ by rw [hg.eq_zero_row hw, comp_zero]

/-- The rows of a bounded matrix meeting a column are finite. -/
lemma finite_support_comp (f : boundedSubmodule X Y) (g : Mat Y Z) (u v : ℤ) :
    (Function.support fun w ↦ f.1 w v ≫ g u w).Finite := by
  obtain ⟨b, hb⟩ := f.2
  refine (window v b).finite_toSet.subset fun w hw ↦ ?_
  by_contra h
  exact (Function.mem_support.mp hw) (by rw [hb.eq_zero_col h, zero_comp])

lemma PropLE.matComp {f : Mat X Y} {g : Mat Y Z} {b c : ℕ} (hf : PropLE f b) (hg : PropLE g c) :
    PropLE (matComp f g) (b + c) := fun u v h ↦ by
  rw [matComp_eq_sum_left hf]
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  refine (hg u w ?_).symm ▸ comp_zero
  simp only [window, Finset.mem_Icc] at hw
  push_cast at h
  rw [lt_abs] at h ⊢
  omega

lemma matComp_mem (f : boundedSubmodule X Y) (g : boundedSubmodule Y Z) :
    matComp f.1 g.1 ∈ boundedSubmodule X Z := by
  obtain ⟨b, hb⟩ := f.2
  obtain ⟨c, hc⟩ := g.2
  exact ⟨_, hb.matComp hc⟩

/-- Associativity; only the outer factors need to be bounded. -/
lemma matComp_assoc {f : Mat X Y} {h : Mat Z T} {b c : ℕ} (hf : PropLE f b) (g : Mat Y Z)
    (hh : PropLE h c) : matComp (matComp f g) h = matComp f (matComp g h) := by
  funext u v
  rw [matComp_eq_sum_right _ hh, matComp_eq_sum_left hf]
  simp_rw [matComp_eq_sum_left hf, matComp_eq_sum_right _ hh, Preadditive.sum_comp, Preadditive.comp_sum,
    Category.assoc]
  exact Finset.sum_comm

lemma matComp_add_left (f f' : Mat X Y) {g : Mat Y Z} {b : ℕ} (hg : PropLE g b) :
    matComp (f + f') g = matComp f g + matComp f' g := by
  funext u v
  simp only [matComp_eq_sum_right _ hg, Pi.add_apply, add_comp, Finset.sum_add_distrib]

lemma matComp_add_right {f : Mat X Y} {b : ℕ} (hf : PropLE f b) (g g' : Mat Y Z) :
    matComp f (g + g') = matComp f g + matComp f g' := by
  funext u v
  simp only [matComp_eq_sum_left hf, Pi.add_apply, comp_add, Finset.sum_add_distrib]

lemma matComp_smul_left (r : ℚ) (f : Mat X Y) {g : Mat Y Z} {b : ℕ} (hg : PropLE g b) :
    matComp (r • f) g = r • matComp f g := by
  funext u v
  simp only [matComp_eq_sum_right _ hg, Pi.smul_apply, Linear.smul_comp, Finset.smul_sum]

lemma matComp_smul_right {f : Mat X Y} {b : ℕ} (hf : PropLE f b) (r : ℚ) (g : Mat Y Z) :
    matComp f (r • g) = r • matComp f g := by
  funext u v
  simp only [matComp_eq_sum_left hf, Pi.smul_apply, Linear.comp_smul, Finset.smul_sum]

/-! ### Diagonal matrices -/

/-- The diagonal matrix with entries `d v`. -/
def diagMat (d : ∀ v, X.obj v ⟶ Y.obj v) : Mat X Y :=
  fun w v ↦ if h : v = w then d v ≫ eqToHom (congrArg Y.obj h) else 0

lemma diagMat_self (d : ∀ v, X.obj v ⟶ Y.obj v) (v : ℤ) : diagMat d v v = d v := by
  rw [diagMat, dite_eq_left rfl, eqToHom_refl, comp_id]

lemma diagMat_ne (d : ∀ v, X.obj v ⟶ Y.obj v) {w v : ℤ} (h : v ≠ w) : diagMat d w v = 0 :=
  dite_eq_right h

lemma propLE_diagMat (d : ∀ v, X.obj v ⟶ Y.obj v) : PropLE (diagMat d) 0 := fun w v h ↦
  diagMat_ne d fun hvw ↦ by subst hvw; simp at h

lemma diagMat_matComp (d : ∀ v, X.obj v ⟶ Y.obj v) (g : Mat Y Z) :
    matComp (diagMat d) g = fun u v ↦ d v ≫ g u v := by
  funext u v
  rw [matComp_eq_sum {v} fun w hw ↦ by
    rw [diagMat_ne d (Ne.symm (Finset.notMem_singleton.mp hw)), zero_comp],
    Finset.sum_singleton, diagMat_self]

lemma matComp_diagMat (f : Mat X Y) (e : ∀ v, Y.obj v ⟶ Z.obj v) :
    matComp f (diagMat e) = fun u v ↦ f u v ≫ e u := by
  funext u v
  rw [matComp_eq_sum {u} fun w hw ↦ by
    rw [diagMat_ne e (Finset.notMem_singleton.mp hw), comp_zero],
    Finset.sum_singleton, diagMat_self]

/-- The identity matrix. -/
def matId (X : Obj A) : Mat X X := diagMat fun v ↦ 𝟙 (X.obj v)

lemma matId_matComp (f : Mat X Y) : matComp (matId X) f = f := by
  rw [matId, diagMat_matComp]; exact funext fun u ↦ funext fun v ↦ id_comp (f u v)

lemma matComp_matId (f : Mat X Y) : matComp f (matId Y) = f := by
  rw [matId, matComp_diagMat]; exact funext fun u ↦ funext fun v ↦ comp_id (f u v)

/-! ### The category -/

instance category : SmallCategory (Obj A) where
  Hom X Y := boundedSubmodule X Y
  id X := ⟨matId X, ⟨0, propLE_diagMat _⟩⟩
  comp f g := ⟨matComp f.1 g.1, matComp_mem f g⟩
  id_comp f := Subtype.ext (matId_matComp f.1)
  comp_id f := Subtype.ext (matComp_matId f.1)
  assoc f g h := Subtype.ext <| by
    obtain ⟨b, hb⟩ := f.2
    obtain ⟨c, hc⟩ := h.2
    exact matComp_assoc hb g.1 hc

lemma comp_mat (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = matComp f.1 g.1 := rfl

lemma id_mat (X : Obj A) : (𝟙 X : X ⟶ X).1 = matId X := rfl

/-- The entries of a composite, as a `finsum`. -/
lemma comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (u v : ℤ) :
    (f ≫ g).1 u v = ∑ᶠ w, f.1 w v ≫ g.1 u w := rfl

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : ∀ w v, f.1 w v = g.1 w v) : f = g :=
  Subtype.ext (funext fun w ↦ funext fun v ↦ h w v)

/-- A bounded matrix as a morphism. -/
def homMk (f : Mat X Y) (b : ℕ) (hf : PropLE f b) : X ⟶ Y := ⟨f, b, hf⟩

@[simp] lemma homMk_apply (f : Mat X Y) (b : ℕ) (hf : PropLE f b) (w v : ℤ) :
    (homMk f b hf).1 w v = f w v := rfl

lemma exists_propLE (f : X ⟶ Y) : ∃ b, PropLE f.1 b := f.2

/-- The entries of a composite over the window of the left factor's bound. -/
lemma comp_apply_left (f : X ⟶ Y) {b : ℕ} (hf : PropLE f.1 b) (g : Y ⟶ Z) (u v : ℤ) :
    (f ≫ g).1 u v = ∑ w ∈ window v b, f.1 w v ≫ g.1 u w :=
  matComp_eq_sum_left hf g.1 u v

/-- The entries of a composite over the window of the right factor's bound. -/
lemma comp_apply_right (f : X ⟶ Y) (g : Y ⟶ Z) {b : ℕ} (hg : PropLE g.1 b) (u v : ℤ) :
    (f ≫ g).1 u v = ∑ w ∈ window u b, f.1 w v ≫ g.1 u w :=
  matComp_eq_sum_right f.1 hg u v

instance preadditive : Preadditive (Obj A) where
  homGroup X Y := inferInstanceAs (AddCommGroup (boundedSubmodule X Y))
  add_comp _ _ _ f f' g := Subtype.ext <| by
    obtain ⟨b, hb⟩ := g.2
    exact matComp_add_left f.1 f'.1 hb
  comp_add _ _ _ f g g' := Subtype.ext <| by
    obtain ⟨b, hb⟩ := f.2
    exact matComp_add_right hb g.1 g'.1

instance linear : Linear ℚ (Obj A) where
  homModule X Y := inferInstanceAs (Module ℚ (boundedSubmodule X Y))
  smul_comp _ _ _ r f g := Subtype.ext <| by
    obtain ⟨b, hb⟩ := g.2
    exact matComp_smul_left r f.1 hb
  comp_smul _ _ _ f r g := Subtype.ext <| by
    obtain ⟨b, hb⟩ := f.2
    exact matComp_smul_right hb r g.1

/-- The entry `(w, v)` as an additive map. -/
def entry (X Y : Obj A) (w v : ℤ) : (X ⟶ Y) →+ (X.obj v ⟶ Y.obj w) where
  toFun f := f.1 w v
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma entry_apply (f : X ⟶ Y) (w v : ℤ) : entry X Y w v f = f.1 w v := rfl

@[simp] lemma zero_apply (w v : ℤ) : (0 : X ⟶ Y).1 w v = 0 := rfl

@[simp] lemma add_apply (f g : X ⟶ Y) (w v : ℤ) : (f + g).1 w v = f.1 w v + g.1 w v := rfl

@[simp] lemma neg_apply (f : X ⟶ Y) (w v : ℤ) : (-f).1 w v = -f.1 w v := rfl

@[simp] lemma sub_apply (f g : X ⟶ Y) (w v : ℤ) : (f - g).1 w v = f.1 w v - g.1 w v := rfl

@[simp] lemma smul_apply (r : ℚ) (f : X ⟶ Y) (w v : ℤ) : (r • f).1 w v = r • f.1 w v := rfl

@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (w v : ℤ) :
    (∑ i ∈ s, f i).1 w v = ∑ i ∈ s, (f i).1 w v :=
  map_sum (entry X Y w v) f s

/-! ### Diagonal morphisms -/

/-- The diagonal morphism with entries `d v`. -/
def diag (d : ∀ v, X.obj v ⟶ Y.obj v) : X ⟶ Y := ⟨diagMat d, 0, propLE_diagMat d⟩

lemma diag_mat (d : ∀ v, X.obj v ⟶ Y.obj v) : (diag d).1 = diagMat d := rfl

@[simp] lemma diag_apply_self (d : ∀ v, X.obj v ⟶ Y.obj v) (v : ℤ) : (diag d).1 v v = d v :=
  diagMat_self d v

lemma diag_apply_ne (d : ∀ v, X.obj v ⟶ Y.obj v) {w v : ℤ} (h : v ≠ w) : (diag d).1 w v = 0 :=
  diagMat_ne d h

@[simp] lemma diag_comp_apply (d : ∀ v, X.obj v ⟶ Y.obj v) (g : Y ⟶ Z) (u v : ℤ) :
    (diag d ≫ g).1 u v = d v ≫ g.1 u v :=
  congrFun (congrFun (diagMat_matComp d g.1) u) v

@[simp] lemma comp_diag_apply (f : X ⟶ Y) (e : ∀ v, Y.obj v ⟶ Z.obj v) (u v : ℤ) :
    (f ≫ diag e).1 u v = f.1 u v ≫ e u :=
  congrFun (congrFun (matComp_diagMat f.1 e) u) v

lemma diag_ext {d d' : ∀ v, X.obj v ⟶ Y.obj v} (h : ∀ v, d v = d' v) : diag d = diag d' :=
  congrArg diag (funext h)

lemma diag_id (X : Obj A) : diag (fun v ↦ 𝟙 (X.obj v)) = 𝟙 X := rfl

lemma diag_comp_diag (d : ∀ v, X.obj v ⟶ Y.obj v) (e : ∀ v, Y.obj v ⟶ Z.obj v) :
    diag d ≫ diag e = diag fun v ↦ d v ≫ e v := by
  ext w v
  rw [diag_comp_apply]
  by_cases h : v = w
  · subst h; rw [diag_apply_self, diag_apply_self]
  · rw [diag_apply_ne _ h, diag_apply_ne _ h, comp_zero]

lemma diag_entrywise {d : ∀ v, X.obj v ⟶ Y.obj v} {f : X ⟶ Y}
    (h : ∀ v, d v = f.1 v v) (h' : ∀ w v, v ≠ w → f.1 w v = 0) : diag d = f := by
  ext w v
  by_cases hvw : v = w
  · subst hvw; rw [diag_apply_self, h]
  · rw [diag_apply_ne _ hvw, h' w v hvw]

lemma diag_zero : diag (fun v ↦ (0 : X.obj v ⟶ Y.obj v)) = 0 :=
  diag_entrywise (fun _ ↦ rfl) fun _ _ _ ↦ rfl

lemma diag_add (d e : ∀ v, X.obj v ⟶ Y.obj v) : diag (fun v ↦ d v + e v) = diag d + diag e :=
  diag_entrywise (fun v ↦ by simp) fun w v h ↦ by simp [diag_apply_ne _ h]

lemma diag_neg (d : ∀ v, X.obj v ⟶ Y.obj v) : diag (fun v ↦ -d v) = -diag d :=
  diag_entrywise (fun v ↦ by simp) fun w v h ↦ by simp [diag_apply_ne _ h]

lemma diag_smul (r : ℚ) (d : ∀ v, X.obj v ⟶ Y.obj v) : diag (fun v ↦ r • d v) = r • diag d :=
  diag_entrywise (fun v ↦ by simp) fun w v h ↦ by simp [diag_apply_ne _ h]

lemma diag_sum {ι : Type*} (s : Finset ι) (d : ι → ∀ v, X.obj v ⟶ Y.obj v) :
    diag (fun v ↦ ∑ i ∈ s, d i v) = ∑ i ∈ s, diag (d i) :=
  diag_entrywise (fun v ↦ by simp) fun w v h ↦ by simp [diag_apply_ne _ h]

/-- The diagonal isomorphism with components `e v`. -/
@[simps]
def diagIso (e : ∀ v, X.obj v ≅ Y.obj v) : X ≅ Y where
  hom := diag fun v ↦ (e v).hom
  inv := diag fun v ↦ (e v).inv
  hom_inv_id := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (e v).hom_inv_id
  inv_hom_id := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (e v).inv_hom_id

/-! ### Zero object and biproducts -/

open ZeroObject in
/-- The zero object: `0` at every position. -/
def zeroObj : Obj A := ⟨fun _ ↦ 0⟩

lemma isZero_of_forall {X : Obj A} (h : ∀ v, IsZero (X.obj v)) : IsZero X :=
  (IsZero.iff_id_eq_zero _).mpr (hom_ext fun _ v ↦ (h v).eq_of_src _ _)

open ZeroObject in
instance hasZeroObject : HasZeroObject (Obj A) :=
  ⟨⟨zeroObj, isZero_of_forall fun _ ↦ isZero_zero _⟩⟩

/-- The pointwise bicone of bicones `b v`. -/
@[simps]
def biconeOf (b : ∀ v, BinaryBicone (X.obj v) (Y.obj v)) : BinaryBicone X Y where
  pt := ⟨fun v ↦ (b v).pt⟩
  fst := diag fun v ↦ (b v).fst
  snd := diag fun v ↦ (b v).snd
  inl := diag fun v ↦ (b v).inl
  inr := diag fun v ↦ (b v).inr
  inl_fst := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (b v).inl_fst
  inl_snd := by rw [diag_comp_diag, ← diag_zero]; exact diag_ext fun v ↦ (b v).inl_snd
  inr_fst := by rw [diag_comp_diag, ← diag_zero]; exact diag_ext fun v ↦ (b v).inr_fst
  inr_snd := by rw [diag_comp_diag, ← diag_id]; exact diag_ext fun v ↦ (b v).inr_snd

/-- Pointwise bilimit bicones form a bilimit bicone. -/
def biconeOfIsBilimit {b : ∀ v, BinaryBicone (X.obj v) (Y.obj v)} (hb : ∀ v, (b v).IsBilimit) :
    (biconeOf b).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    simp only [biconeOf_fst, biconeOf_inl, biconeOf_snd, biconeOf_inr]
    erw [diag_comp_diag, diag_comp_diag, ← diag_add, ← diag_id]
    exact diag_ext fun v ↦ IsBilimit.binary_total (hb v)

instance hasBinaryBiproducts : HasBinaryBiproducts (Obj A) :=
  ⟨fun X Y ↦ HasBinaryBiproduct.mk
    ⟨_, biconeOfIsBilimit fun v ↦ (A.unitary (X.obj v) (Y.obj v)).some.isBilimit⟩⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (Obj A) := hasFiniteBiproducts_of_binary

/-! ### The involution -/

/-- Entrywise transpose of matrices: `(starMat f) v w = (f w v)^*`. -/
def starMat (f : Mat X Y) : Mat Y X := fun v w ↦ A.inv.star (f w v)

lemma PropLE.starMat {f : Mat X Y} {b : ℕ} (hf : PropLE f b) : PropLE (starMat f) b :=
  fun v w h ↦ by
    change A.inv.star (f w v) = 0
    rw [hf w v (by rwa [abs_sub_comm]), A.inv.star_zero]

lemma star_finsetSum {P Q : A} {ι : Type*} (s : Finset ι) (f : ι → (P ⟶ Q)) :
    A.inv.star (∑ i ∈ s, f i) = ∑ i ∈ s, A.inv.star (f i) :=
  map_sum (A.inv.starHom P Q) f s

lemma starMat_matComp {f : Mat X Y} {b : ℕ} (hf : PropLE f b) (g : Mat Y Z) :
    starMat (matComp f g) = matComp (starMat g) (starMat f) := by
  funext w v
  change A.inv.star (matComp f g v w) = _
  rw [matComp_eq_sum_left hf, matComp_eq_sum_right _ hf.starMat, star_finsetSum]
  exact Finset.sum_congr rfl fun x _ ↦ A.inv.star_comp _ _

lemma starMat_diagMat (d : ∀ v, X.obj v ⟶ Y.obj v) :
    starMat (diagMat d) = diagMat fun v ↦ A.inv.star (d v) := by
  funext w v
  change A.inv.star (diagMat d v w) = _
  by_cases h : v = w
  · subst h; rw [diagMat_self, diagMat_self]
  · rw [diagMat_ne _ (Ne.symm h), diagMat_ne _ h, A.inv.star_zero]

lemma starMat_mem (f : X ⟶ Y) : starMat f.1 ∈ boundedSubmodule Y X :=
  f.2.elim fun _ hb ↦ ⟨_, hb.starMat⟩

/-- The entrywise transpose of a morphism. -/
def star (f : X ⟶ Y) : Y ⟶ X := ⟨starMat f.1, starMat_mem f⟩

/-- The induced object-fixing strict involution. -/
def involution : StrictInvolution (Obj A) where
  star := star
  star_comp f g := Subtype.ext <| f.2.elim fun _ hb ↦ starMat_matComp hb g.1
  star_id X := Subtype.ext (starMat_diagMat _ |>.trans <| congrArg diagMat <|
    funext fun v ↦ A.inv.star_id (X.obj v))
  star_add _ _ := Subtype.ext <| funext fun _ ↦ funext fun _ ↦ A.inv.star_add _ _
  star_star _ := Subtype.ext <| funext fun _ ↦ funext fun _ ↦ A.inv.star_star _

@[simp] lemma star_apply (f : X ⟶ Y) (w v : ℤ) :
    (involution.star f).1 w v = A.inv.star (f.1 v w) := rfl

lemma star_diag (d : ∀ v, X.obj v ⟶ Y.obj v) :
    involution.star (diag d) = diag fun v ↦ A.inv.star (d v) :=
  Subtype.ext (starMat_diagMat d)

/-- The pointwise unitary bicone. -/
@[simps! toBinaryBicone]
def unitaryBicone (b : ∀ v, UnitaryBicone A.inv (X.obj v) (Y.obj v)) :
    UnitaryBicone involution X Y where
  toBinaryBicone := biconeOf fun v ↦ (b v).toBinaryBicone
  isBilimit := biconeOfIsBilimit fun v ↦ (b v).isBilimit
  star_inl := by
    rw [biconeOf_inl, biconeOf_fst]; erw [star_diag]; exact diag_ext fun v ↦ (b v).star_inl
  star_inr := by
    rw [biconeOf_inr, biconeOf_snd]; erw [star_diag]; exact diag_ext fun v ↦ (b v).star_inr

/-- Pointwise unitary bicones are unitary. -/
lemma unitary (X Y : Obj A) : Nonempty (UnitaryBicone involution X Y) :=
  ⟨unitaryBicone fun v ↦ (A.unitary (X.obj v) (Y.obj v)).some⟩

end CZ

/-- **The bounded category** `C_ℤ(A)` [PW85; Ran92, §§4, 15] as an `InvCat`.  Reducible, so the
`CZ` API (stated for `CZ.Obj A`) applies to `A.cz`. -/
abbrev InvCat.cz (A : InvCat) : InvCat where
  carrier := CZ.Obj A
  inv := CZ.involution
  unitary := CZ.unitary

end

end HSFormal.LTheory
