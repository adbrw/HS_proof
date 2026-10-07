import HSFormal.LTheory.KaroubiFiltration

/-!
# Laurent extensions of additive categories (NegKHigh, module N1)

`blueprint/negK-high.md` §2 "Laurent extension", §7 row N1; review `negK-high-review.md` GAP G2.

**Bundling (fix G2).**  `AddCat` bundles a type with a category, preadditive and finite biproduct
structure (`AddStr`).  Instance search cannot unfold a recursion on a variable `l`, so the
iterated extension `Lpow l D` is again an `AddCat` and all instances on `(Lpow l D).carrier` are
the bundled ones (`AddCat.category`, ...).

**Same objects.**  `Laurent D` has *the same carrier* as `D` (only the morphisms change), and so
does `Lpow l D`, definitionally for every `l`:
* `Lpow_carrier : (Lpow l D).carrier = D.carrier` is `rfl`;
* the frozen unfoldings `Lpow_zero : Lpow 0 D = D` and `Lpow_succ : Lpow (l+1) D = Lpow l (Laurent D)`
  are `rfl` (the newest variable is the innermost one);
* `Lpow.map l F` and `Lpow.incl l D` act on objects by `F.obj` resp. the identity, again
  definitionally (`Lpow.map_obj`, `Lpow.incl_obj` are `rfl`).

Hence an object of `Lpow l Y.cz` *is* an object of `Y.cz` (supports, cuts, half-line membership
apply verbatim), and `Kar(Lpow l (Laurent Y)) = Kar(Lpow (l+1) Y)` holds by `rfl`.

**Hom types and transparency.**  Since the carriers coincide, a type ascription `(X : Lpow l D)`
does *not* select the category structure.  Morphisms in a given bundled category are written
`D.Mor X Y` (`AddCat.Mor`, an abbreviation for `@Quiver.Hom D.carrier _ X Y`), e.g.
`(Lpow l D).Mor X Y`; identities `D.idMor X` (`𝟙 X` takes the category from the type of `X`).
`Laurent`, `Lpow` and `LpowStr` are `@[instance_reducible]`: type class search and `rw`/`simp`
see `(Lpow l D).carrier = D.carrier` (so objects of either type can be used in hom types of
either category) and identify the instances of `Lpow (l+1) D` and `Lpow l (Laurent D)`, while
discrimination-tree keys keep the categories apart.  The functors `Laurent.incl`, `Laurent.map`,
`Lpow.incl`, `Lpow.map` are `@[instance_reducible]` too (their `obj` unfolds when implicit arguments
are compared).  A unification hint (`toAddCat_carrier_hint`) lets `Lpow.map l Φ.F` elaborate for a
functor `Φ` of `InvCat`s.

**Contents.**
* `Laurent D`: `Hom(X, Y) = ℤ →₀ Hom_D(X, Y)` with convolution; `Laurent.coeff`, `Laurent.single`,
  `Laurent.ext`, `Laurent.coeff_comp`, `Laurent.incl` (degree `0`, faithful), the monomials
  `Laurent.T n` (central, `T m ≫ T n = T (m + n)`, `T 0 = 𝟙`), `Laurent.map F` (coefficientwise,
  additive, `Laurent.map_comp`/`map_id`), `Laurent.mapNatTrans`, `Laurent.fullyFaithfulMap`.
* `Lpow l D`, `Lpow.map l F`, `Lpow.incl l D`, `Lpow.mapNatTrans`, `Lpow.mapNatIso`,
  `Lpow.mapIdIso`, `Lpow.mapCompIso`, `Lpow.fullyFaithfulMap`, `Lpow.extend` (the old variables
  `L^l D ⥤ L^{l+1} D`), `Lpow.w` (powers of the newest variable, central), and the coefficient
  calculus `Lpow.coeff γ` (`γ : Fin l → ℤ`, `γ 0` the newest variable): `Lpow.ext`,
  `coeff_incl`, `coeff_incl_comp`, `coeff_comp_incl`, `coeff_map`, `coeff_comp_mem`
  (coefficients of a composite lie in every additive submonoid containing all products of
  coefficients), `finite_coeff_support`, `exists_bound_coeff`.
* `LaurentPos D` (`L⁺ D`): the Laurent morphisms without negative coefficients, with the faithful
  inclusion `LaurentPos.incl D : L⁺ D ⥤ L D` and `LaurentPos.coeff_incl_map_neg`.
* `InvCat.toAddCat` (a coercion): the underlying bundled additive category of an `InvCat`, with
  `Lpow 0 ↑Y = ↑Y` and instances definitionally those of `Y`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive

noncomputable section

universe v u v' u' v'' u''

/-! ### Bundled additive categories -/

/-- An additive category structure (category, preadditive, finite biproducts) on a fixed type. -/
structure AddStr (α : Type u) where
  [cat : Category.{v} α]
  [preadd : Preadditive α]
  [biprod : HasFiniteBiproducts α]

/-- A bundled additive category (preadditive with finite biproducts). -/
structure AddCat where
  /-- The objects. -/
  carrier : Type u
  /-- The additive structure. -/
  str : AddStr.{v} carrier

namespace AddCat

instance : CoeSort AddCat.{v, u} (Type u) := ⟨carrier⟩

instance category (D : AddCat.{v, u}) : Category.{v} D.carrier := D.str.cat

instance preadditive (D : AddCat.{v, u}) : Preadditive D.carrier := D.str.preadd

instance hasFiniteBiproducts (D : AddCat.{v, u}) : HasFiniteBiproducts D.carrier := D.str.biprod

instance hasBinaryBiproducts (D : AddCat.{v, u}) : HasBinaryBiproducts D.carrier :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- Morphisms of the bundled category `D`, between objects given in any type definitionally equal
to `D.carrier` (e.g. objects of `Lpow l D` or `Laurent D`). -/
abbrev Mor (D : AddCat.{v, u}) (X Y : D.carrier) : Type v := X ⟶ Y

/-- The identity of `X` in `D`, for `X` given in a type definitionally equal to `D.carrier`
(`𝟙 X` selects the category structure from the type of `X`). -/
abbrev idMor (D : AddCat.{v, u}) (X : D.carrier) : D.Mor X X := 𝟙 X

/-- The bundled additive category of a type with instances. -/
abbrev of (α : Type u) [Category.{v} α] [Preadditive α] [HasFiniteBiproducts α] :
    AddCat.{v, u} :=
  ⟨α, {}⟩

lemma of_carrier (α : Type u) [Category.{v} α] [Preadditive α] [HasFiniteBiproducts α] :
    (of α).carrier = α := rfl

/-- `AddCat` is determined by its fields (structure eta). -/
lemma eta (D : AddCat.{v, u}) : (⟨D.carrier, D.str⟩ : AddCat.{v, u}) = D := rfl

end AddCat

/-- The underlying bundled additive category of an `InvCat`.  Instance-reducible: instances on its
carrier are found as the bundled ones (`AddCat.category ↑Y`, so generic `AddCat` instances and
lemmas apply), and they unfold to those of `Y` during instance search and `rw`/`simp`. -/
@[coe, instance_reducible]
def InvCat.toAddCat (Y : InvCat) : AddCat.{0, 0} := ⟨Y.carrier, {}⟩

instance : Coe InvCat AddCat.{0, 0} := ⟨InvCat.toAddCat⟩

lemma InvCat.toAddCat_carrier (Y : InvCat) : (Y : AddCat.{0, 0}).carrier = Y.carrier := rfl

/-- Unification hint: `AddCat.carrier ?D =?= Y.carrier` is solved by `?D := ↑Y`, so that functors
`Φ.F : Y.carrier ⥤ B.carrier` of `InvCat`s can be passed to `Laurent.map`/`Lpow.map` without
naming the bundled categories. -/
unif_hint toAddCat_carrier_hint (D : AddCat.{0, 0}) (Y : InvCat) where
  D =?= InvCat.toAddCat Y
  ⊢ AddCat.carrier D =?= InvCat.carrier Y

/-! ### The Laurent extension -/

namespace Laurent

variable {D : AddCat.{v, u}}

/-- Convolution of Laurent coefficient families: `(f * g)_n = ∑_{i + j = n} f_i ≫ g_j`. -/
def conv {X Y Z : D} : (ℤ →₀ D.Mor X Y) →+ (ℤ →₀ D.Mor Y Z) →+ (ℤ →₀ D.Mor X Z) :=
  Finsupp.liftAddHom fun i ↦
    (Finsupp.liftAddHom fun j ↦
      ((Preadditive.compHom : D.Mor X Y →+ D.Mor Y Z →+ D.Mor X Z).compr₂
        (Finsupp.singleAddHom (i + j))).flip).flip

lemma conv_single_single {X Y Z : D} (i j : ℤ) (a : D.Mor X Y) (b : D.Mor Y Z) :
    conv (Finsupp.single i a) (Finsupp.single j b) = Finsupp.single (i + j) (a ≫ b) := by
  simp [conv]; rfl

lemma conv_assoc {X Y Z T : D} (f : ℤ →₀ D.Mor X Y) (g : ℤ →₀ D.Mor Y Z) (h : ℤ →₀ D.Mor Z T) :
    conv (conv f g) h = conv f (conv g h) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, AddMonoidHom.add_apply, hf, hf']
  | single i a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [map_add, AddMonoidHom.add_apply, hg, hg']
    | single j b =>
      induction h using Finsupp.induction_linear with
      | zero => simp
      | add h h' hh hh' => simp only [map_add, hh, hh']
      | single k c => simp only [conv_single_single, assoc, add_assoc]

lemma conv_single_zero_left {X Y Z : D} (a : D.Mor X Y) (g : ℤ →₀ D.Mor Y Z) :
    conv (Finsupp.single 0 a) g = g.mapRange (fun b ↦ a ≫ b) (comp_zero) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' =>
    rw [map_add, hg, hg', Finsupp.mapRange_add (fun _ _ ↦ comp_add _ _ _ _ _ _)]
  | single j b => rw [conv_single_single, zero_add, Finsupp.mapRange_single]

lemma conv_single_zero_right {X Y Z : D} (f : ℤ →₀ D.Mor X Y) (b : D.Mor Y Z) :
    conv f (Finsupp.single 0 b) = f.mapRange (fun a ↦ a ≫ b) (zero_comp) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    rw [map_add, AddMonoidHom.add_apply, hf, hf',
      Finsupp.mapRange_add (fun _ _ ↦ add_comp _ _ _ _ _ _)]
  | single i a => rw [conv_single_single, add_zero, Finsupp.mapRange_single]

lemma conv_apply_sum {X Y Z : D} (f : ℤ →₀ D.Mor X Y) (g : ℤ →₀ D.Mor Y Z) (n : ℤ) :
    conv f g n = f.sum fun i a ↦ a ≫ g (n - i) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    rw [map_add, AddMonoidHom.add_apply, Finsupp.add_apply, hf, hf',
      Finsupp.sum_add_index' (fun _ ↦ zero_comp) (fun _ _ _ ↦ add_comp _ _ _ _ _ _)]
  | single i a =>
    rw [Finsupp.sum_single_index zero_comp]
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => rw [map_add, Finsupp.add_apply, hg, hg', Finsupp.add_apply, comp_add]
    | single j b =>
      rw [conv_single_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : i + j = n
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega), comp_zero]

/-- The coefficients of a convolution, summed over any window containing the support of the left
factor. -/
lemma conv_apply {X Y Z : D} (f : ℤ →₀ D.Mor X Y) (g : ℤ →₀ D.Mor Y Z) (n : ℤ) (s : Finset ℤ)
    (hs : f.support ⊆ s) : conv f g n = ∑ i ∈ s, f i ≫ g (n - i) := by
  rw [conv_apply_sum, Finsupp.sum_of_support_subset f hs (fun i a ↦ a ≫ g (n - i))
    fun _ _ ↦ zero_comp]

variable (D) in
/-- Type synonym carrying the Laurent category structure during its construction (internal; use
`Laurent D`). -/
def Obj : Type u := D.carrier

/-- The Laurent category structure (internal; use `Laurent D`). -/
@[instance_reducible]
def categoryObj : Category.{v} (Obj D) where
  Hom (X Y : D) := ℤ →₀ D.Mor X Y
  id (X : D) := Finsupp.single 0 (𝟙 X)
  comp {X Y Z : D} f g := conv f g
  id_comp {X Y : D} f := by
    rw [conv_single_zero_left]
    ext n
    simp
  comp_id {X Y : D} f := by
    rw [conv_single_zero_right]
    ext n
    simp
  assoc {X Y Z T : D} f g h := conv_assoc f g h

attribute [local instance] categoryObj

/-- The Laurent preadditive structure (internal). -/
@[instance_reducible]
def preadditiveObj : Preadditive (Obj D) where
  homGroup (X Y : D) := inferInstanceAs (AddCommGroup (ℤ →₀ D.Mor X Y))
  add_comp {X Y Z : D} (f f' : ℤ →₀ D.Mor X Y) (g : ℤ →₀ D.Mor Y Z) :=
    DFunLike.congr_fun (map_add conv f f') g
  comp_add {X Y Z : D} (f : ℤ →₀ D.Mor X Y) (g g' : ℤ →₀ D.Mor Y Z) := map_add (conv f) g g'

attribute [local instance] preadditiveObj

/-- The degree-`0` inclusion (internal). -/
@[instance_reducible]
def inclObj : D.carrier ⥤ Obj D where
  obj X := X
  map f := Finsupp.single 0 f
  map_id _ := rfl
  map_comp f g := by
    change _ = conv _ _
    rw [conv_single_single, add_zero]

instance : (inclObj (D := D)).Additive where
  map_add := Finsupp.single_add _ _ _

lemma hasBinaryBiproducts_obj : HasBinaryBiproducts (Obj D) :=
  ⟨fun (X Y : D) ↦ HasBinaryBiproduct.mk
    { bicone := inclObj.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfTotal _ <| by
        change conv (Finsupp.single 0 (biprod.fst : D.Mor (X ⊞ Y) X))
            (Finsupp.single 0 (biprod.inl : D.Mor X (X ⊞ Y))) +
          conv (Finsupp.single 0 (biprod.snd : D.Mor (X ⊞ Y) Y))
            (Finsupp.single 0 (biprod.inr : D.Mor Y (X ⊞ Y))) = Finsupp.single 0 (𝟙 (X ⊞ Y))
        rw [conv_single_single, conv_single_single, ← Finsupp.single_add, add_zero,
          biprod.total] }⟩

open ZeroObject in
lemma hasFiniteBiproducts_obj : HasFiniteBiproducts (Obj D) := by
  have := hasBinaryBiproducts_obj (D := D)
  have : HasZeroObject (Obj D) :=
    ⟨⟨inclObj.obj (0 : D.carrier), inclObj.map_isZero (isZero_zero _)⟩⟩
  exact hasFiniteBiproducts_of_binary

variable (D) in
/-- The Laurent additive structure on `D.carrier` (internal; use `Laurent D`). -/
def str : AddStr.{v} D.carrier :=
  @AddStr.mk (Obj D) categoryObj preadditiveObj hasFiniteBiproducts_obj

end Laurent

/-- **The Laurent extension** `L D` of an additive category `D`: the same objects, and
`Hom_{L D}(X, Y) = ℤ →₀ Hom_D(X, Y)` with convolution `(f ≫ g)_n = ∑_{i + j = n} f_i ≫ g_j`. -/
@[instance_reducible]
def Laurent (D : AddCat.{v, u}) : AddCat.{v, u} := ⟨D.carrier, Laurent.str D⟩


namespace Laurent

variable {D : AddCat.{v, u}} {D' : AddCat.{v', u'}} {D'' : AddCat.{v'', u''}}
  {X Y Z : Laurent D}

lemma carrier_eq (D : AddCat.{v, u}) : (Laurent D).carrier = D.carrier := rfl

/-- Laurent morphisms are finitely supported families of coefficients. -/
def toFinsupp : (Laurent D).Mor X Y ≃+ (ℤ →₀ D.Mor X Y) := AddEquiv.refl _

lemma toFinsupp_comp (f : (Laurent D).Mor X Y) (g : (Laurent D).Mor Y Z) :
    toFinsupp (f ≫ g) = conv (toFinsupp f) (toFinsupp g) := rfl

lemma toFinsupp_id (X : Laurent D) : toFinsupp (𝟙 X) = Finsupp.single 0 (D.idMor X) := rfl

/-- The coefficient of `wⁿ`. -/
def coeff (n : ℤ) : (Laurent D).Mor X Y →+ D.Mor X Y :=
  (Finsupp.applyAddHom n).comp toFinsupp.toAddMonoidHom

lemma coeff_apply (n : ℤ) (f : (Laurent D).Mor X Y) : coeff n f = toFinsupp f n := rfl

@[ext]
lemma ext {f g : (Laurent D).Mor X Y} (h : ∀ n, coeff n f = coeff n g) : f = g :=
  toFinsupp.injective (Finsupp.ext h)

/-- The support of a Laurent morphism. -/
def support (f : (Laurent D).Mor X Y) : Finset ℤ := (toFinsupp f).support

lemma mem_support_iff {f : (Laurent D).Mor X Y} {n : ℤ} : n ∈ support f ↔ coeff n f ≠ 0 :=
  Finsupp.mem_support_iff

lemma coeff_eq_zero_of_notMem_support {f : (Laurent D).Mor X Y} {n : ℤ} (h : n ∉ support f) :
    coeff n f = 0 :=
  Finsupp.notMem_support_iff.mp h

/-- The monomial `a wⁿ`. -/
def single (n : ℤ) (a : D.Mor X Y) : (Laurent D).Mor X Y := toFinsupp.symm (Finsupp.single n a)

lemma coeff_single (n m : ℤ) (a : D.Mor X Y) :
    coeff m (single n a) = if n = m then a else 0 :=
  Finsupp.single_apply

@[simp] lemma coeff_single_self (n : ℤ) (a : D.Mor X Y) : coeff n (single n a) = a :=
  Finsupp.single_eq_same

lemma coeff_single_ne {n m : ℤ} (h : n ≠ m) (a : D.Mor X Y) : coeff m (single n a) = 0 :=
  Finsupp.single_eq_of_ne' h

@[simp] lemma single_zero (n : ℤ) : single n (0 : D.Mor X Y) = 0 := by
  simp [single]

lemma single_add (n : ℤ) (a b : D.Mor X Y) : single n (a + b) = single n a + single n b := by
  simp [single, Finsupp.single_add]

lemma single_neg (n : ℤ) (a : D.Mor X Y) : single n (-a) = -single n a := by
  simp [single]

lemma single_sub (n : ℤ) (a b : D.Mor X Y) : single n (a - b) = single n a - single n b := by
  simp [single, Finsupp.single_sub]

/-- Induction on Laurent morphisms: monomials and sums. -/
@[elab_as_elim]
lemma induction_linear {motive : (Laurent D).Mor X Y → Prop} (f : (Laurent D).Mor X Y)
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (single : ∀ n a, motive (single n a)) : motive f := by
  obtain ⟨f, rfl⟩ := toFinsupp.symm.surjective f
  induction f using Finsupp.induction_linear with
  | zero => exact zero
  | add f g hf hg => rw [map_add]; exact add _ _ hf hg
  | single n a => exact single n a

lemma single_comp_single (m n : ℤ) (a : D.Mor X Y) (b : D.Mor Y Z) :
    single m a ≫ single n b = single (m + n) (a ≫ b) :=
  conv_single_single m n a b

lemma id_eq_single (X : Laurent D) : 𝟙 X = single 0 (D.idMor X) := rfl

@[simp] lemma coeff_zero (n : ℤ) : coeff n (0 : (Laurent D).Mor X Y) = 0 := rfl

lemma coeff_add (n : ℤ) (f g : (Laurent D).Mor X Y) : coeff n (f + g) = coeff n f + coeff n g :=
  map_add _ _ _

lemma coeff_sub (n : ℤ) (f g : (Laurent D).Mor X Y) : coeff n (f - g) = coeff n f - coeff n g :=
  map_sub _ _ _

lemma coeff_neg (n : ℤ) (f : (Laurent D).Mor X Y) : coeff n (-f) = -coeff n f :=
  map_neg _ _

lemma coeff_sum {ι : Type*} (s : Finset ι) (n : ℤ) (f : ι → (Laurent D).Mor X Y) :
    coeff n (∑ i ∈ s, f i) = ∑ i ∈ s, coeff n (f i) :=
  map_sum _ _ _

/-- **Coefficients of a composite**, summed over any window containing the support of the left
factor. -/
lemma coeff_comp (f : (Laurent D).Mor X Y) (g : (Laurent D).Mor Y Z) (n : ℤ) (s : Finset ℤ)
    (hs : support f ⊆ s) : coeff n (f ≫ g) = ∑ i ∈ s, coeff i f ≫ coeff (n - i) g :=
  conv_apply _ _ n s hs

/-- Coefficients of a composite lie in every additive submonoid containing all products of
coefficients. -/
lemma coeff_comp_mem (f : (Laurent D).Mor X Y) (g : (Laurent D).Mor Y Z)
    (S : AddSubmonoid (D.Mor X Z)) (h : ∀ i j, coeff i f ≫ coeff j g ∈ S) (n : ℤ) :
    coeff n (f ≫ g) ∈ S := by
  rw [coeff_comp f g n _ subset_rfl]
  exact S.sum_mem fun i _ ↦ h _ _

lemma coeff_id (n : ℤ) (X : Laurent D) :
    coeff n (𝟙 X) = if (0 : ℤ) = n then D.idMor X else 0 :=
  coeff_single 0 n _

/-! #### The degree-`0` inclusion -/

variable (D) in
/-- The degree-`0` inclusion `ι : D ⥤ L D` (identity on objects). -/
@[instance_reducible]
def incl : D.carrier ⥤ (Laurent D).carrier := inclObj

@[simp] lemma incl_obj (X : D) : (incl D).obj X = X := rfl

lemma incl_map (a : D.Mor X Y) : (incl D).map a = single 0 a := rfl

instance : (incl D).Additive where
  map_add {X Y f g} := single_add (X := X) (Y := Y) 0 f g

lemma coeff_incl (n : ℤ) (a : D.Mor X Y) :
    coeff n ((incl D).map a) = if (0 : ℤ) = n then a else 0 :=
  coeff_single 0 n a

@[simp] lemma coeff_zero_incl (a : D.Mor X Y) : coeff 0 ((incl D).map a) = a :=
  coeff_single_self 0 a

instance : (incl D).Faithful where
  map_injective {X Y} a b h := by
    have := congrArg (coeff (X := X) (Y := Y) 0) h
    rwa [coeff_zero_incl, coeff_zero_incl] at this

lemma incl_comp_single (a : D.Mor X Y) (n : ℤ) (b : D.Mor Y Z) :
    (incl D).map a ≫ single n b = single n (a ≫ b) := by
  rw [incl_map, single_comp_single, zero_add]

lemma single_comp_incl (n : ℤ) (a : D.Mor X Y) (b : D.Mor Y Z) :
    single n a ≫ (incl D).map b = single n (a ≫ b) := by
  rw [incl_map, single_comp_single, add_zero]

lemma coeff_incl_comp (a : D.Mor X Y) (f : (Laurent D).Mor Y Z) (n : ℤ) :
    coeff n ((incl D).map a ≫ f) = a ≫ coeff n f := by
  induction f using induction_linear with
  | zero => simp
  | add f g hf hg => rw [comp_add, coeff_add, coeff_add, hf, hg, comp_add]
  | single m b =>
    rw [incl_comp_single, coeff_single, coeff_single]
    split_ifs <;> simp

lemma coeff_comp_incl (f : (Laurent D).Mor X Y) (b : D.Mor Y Z) (n : ℤ) :
    coeff n (f ≫ (incl D).map b) = coeff n f ≫ b := by
  induction f using induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_comp, coeff_add, coeff_add, hf, hg, add_comp]
  | single m a =>
    rw [single_comp_incl, coeff_single, coeff_single]
    split_ifs <;> simp

/-! #### Monomials `wⁿ` -/

/-- The monomial `wⁿ = 𝟙 wⁿ` on `X`; `w = T 1` is central and invertible. -/
def T (n : ℤ) (X : Laurent D) : (Laurent D).Mor X X := single n (D.idMor X)

lemma T_zero (X : Laurent D) : T 0 X = 𝟙 X := rfl

lemma T_comp_T (m n : ℤ) (X : Laurent D) : T m X ≫ T n X = T (m + n) X := by
  rw [T, T, single_comp_single]
  exact congrArg _ (id_comp _)

lemma T_comp_T_neg (n : ℤ) (X : Laurent D) : T n X ≫ T (-n) X = 𝟙 X := by
  rw [T_comp_T, add_neg_cancel, T_zero]

lemma T_neg_comp_T (n : ℤ) (X : Laurent D) : T (-n) X ≫ T n X = 𝟙 X := by
  rw [T_comp_T, neg_add_cancel, T_zero]

/-- `wⁿ` is central. -/
lemma T_comm (n : ℤ) (f : (Laurent D).Mor X Y) : T n X ≫ f = f ≫ T n Y := by
  induction f using induction_linear with
  | zero => simp
  | add f g hf hg => rw [comp_add, add_comp, hf, hg]
  | single m a =>
    rw [T, T, single_comp_single, single_comp_single, add_comm]
    exact congrArg _ ((id_comp a).trans (comp_id a).symm)

lemma single_eq_incl_comp_T (n : ℤ) (a : D.Mor X Y) : single n a = (incl D).map a ≫ T n Y := by
  rw [T, incl_comp_single]
  exact congrArg _ (comp_id a).symm

lemma coeff_T_comp (m n : ℤ) (f : (Laurent D).Mor X Y) :
    coeff m (T n X ≫ f) = coeff (m - n) f := by
  induction f using induction_linear with
  | zero => simp
  | add f g hf hg => rw [comp_add, coeff_add, coeff_add, hf, hg]
  | single k a =>
    rw [T, single_comp_single, coeff_single, coeff_single]
    by_cases h : k = m - n
    · rw [ite_eq_left (by omega), ite_eq_left h]
      exact id_comp a
    · rw [ite_eq_right (by omega), ite_eq_right h]

/-- The monomial `wⁿ` as an isomorphism. -/
@[simps]
def TIso (n : ℤ) (X : Laurent D) : X ≅ X where
  hom := T n X
  inv := T (-n) X
  hom_inv_id := T_comp_T_neg n X
  inv_hom_id := T_neg_comp_T n X

/-! #### Coefficientwise functors -/

/-- `L F`: the coefficientwise extension of an additive functor (`F.obj` on objects). -/
@[instance_reducible]
def map (F : D.carrier ⥤ D'.carrier) [F.Additive] : (Laurent D).carrier ⥤ (Laurent D').carrier where
  obj X := F.obj X
  map {X Y} f := toFinsupp.symm ((toFinsupp f).mapRange F.map (F.map_zero _ _))
  map_id X := by
    apply toFinsupp.injective
    simp only [toFinsupp_id, AddEquiv.apply_symm_apply, Finsupp.mapRange_single]
    exact congrArg _ (F.map_id X)
  map_comp {X Y Z} f g := by
    apply ext
    intro n
    rw [coeff_comp _ _ n (support f) (fun i hi ↦ by
      simp only [support, AddEquiv.apply_symm_apply, Finsupp.mem_support_iff,
        Finsupp.mapRange_apply, ne_eq] at hi ⊢
      exact fun h ↦ hi (by rw [h, F.map_zero]))]
    simp only [coeff_apply, toFinsupp_comp, AddEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    rw [conv_apply _ _ n (support f) subset_rfl, F.map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ F.map_comp _ _

variable (F : D.carrier ⥤ D'.carrier) [F.Additive]

@[simp] lemma map_obj (X : Laurent D) : (map F).obj X = F.obj X := rfl

@[simp] lemma coeff_map (n : ℤ) (f : (Laurent D).Mor X Y) :
    coeff n ((map F).map f) = F.map (coeff n f) := by
  simp [coeff_apply, map]

instance : (map F).Additive where
  map_add {X Y f g} := ext fun n ↦ by
    rw [coeff_map, coeff_add, coeff_add, coeff_map, coeff_map, F.map_add]

lemma map_single (n : ℤ) (a : D.Mor X Y) : (map F).map (single n a) = single n (F.map a) :=
  ext fun m ↦ by rw [coeff_map, coeff_single, coeff_single]; split_ifs <;> simp

lemma map_incl (a : D.Mor X Y) : (map F).map ((incl D).map a) = (incl D').map (F.map a) :=
  map_single F 0 a

lemma map_T (n : ℤ) (X : Laurent D) : (map F).map (T n X) = T n (F.obj X) := by
  rw [T, map_single]
  exact congrArg _ (F.map_id X)

lemma map_id_map (f : (Laurent D).Mor X Y) : (map (𝟭 D.carrier)).map f = f :=
  ext fun n ↦ by rw [coeff_map]; rfl

lemma map_comp_map (G : D'.carrier ⥤ D''.carrier) [G.Additive] (f : (Laurent D).Mor X Y) :
    (map (F ⋙ G)).map f = (map G).map ((map F).map f) :=
  ext fun n ↦ by rw [coeff_map, coeff_map G, coeff_map F]; rfl

/-- `L η`: the coefficientwise extension of a natural transformation (degree `0`). -/
@[simps]
def mapNatTrans {F G : D.carrier ⥤ D'.carrier} [F.Additive] [G.Additive] (η : F ⟶ G) :
    map F ⟶ map G where
  app X := (incl D').map (η.app X)
  naturality {X Y} f := ext fun n ↦ by
    change coeff n ((map F).map f ≫ (incl D').map (η.app Y)) =
      coeff n ((incl D').map (η.app X) ≫ (map G).map f)
    rw [coeff_comp_incl, coeff_incl_comp, coeff_map, coeff_map, η.naturality]

/-- `L F` is fully faithful if `F` is. -/
def fullyFaithfulMap {F : D.carrier ⥤ D'.carrier} [F.Additive] (hF : F.FullyFaithful) :
    (map F).FullyFaithful where
  preimage {X Y} f := toFinsupp.symm ((toFinsupp f).mapRange hF.preimage
    (hF.map_injective (by rw [hF.map_preimage, F.map_zero])))
  map_preimage {X Y} f := ext fun n ↦ by
    rw [coeff_map]
    simp [coeff_apply]
  preimage_map {X Y} f := ext fun n ↦ by
    simp only [coeff_apply, AddEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    exact hF.preimage_map _

instance [F.Faithful] : (map F).Faithful where
  map_injective {X Y} f g h := ext fun n ↦ F.map_injective <| by
    rw [← coeff_map, ← coeff_map, h]

end Laurent

/-! ### Iterated Laurent extensions -/

/-- The additive structure of the `l`-fold Laurent extension, on the fixed carrier `D.carrier`
(newest variable innermost).  Instance-reducible, so that instance arguments of `L^{l+1} D` and
`L^l (L D)` are identified by `rw`/`simp`. -/
@[instance_reducible]
def LpowStr : ℕ → (D : AddCat.{v, u}) → AddStr.{v} D.carrier
  | 0, D => D.str
  | l + 1, D => LpowStr l (Laurent D)

/-- **The iterated Laurent extension** `L^l D`, bundled (review fix G2).  Its objects are those
of `D` (`Lpow_carrier`), and the unfoldings `Lpow 0 D = D`, `Lpow (l + 1) D = Lpow l (Laurent D)`
hold by `rfl` (`Lpow_zero`, `Lpow_succ`): the newest Laurent variable is the innermost one. -/
@[instance_reducible]
def Lpow (l : ℕ) (D : AddCat.{v, u}) : AddCat.{v, u} := ⟨D.carrier, LpowStr l D⟩

/-- Frozen unfolding: `L^0 D = D` (definitional). -/
theorem Lpow_zero (D : AddCat.{v, u}) : Lpow 0 D = D := rfl

/-- Frozen unfolding: `L^{l+1} D = L^l (L D)` (definitional). -/
theorem Lpow_succ (l : ℕ) (D : AddCat.{v, u}) : Lpow (l + 1) D = Lpow l (Laurent D) := rfl

/-- The objects of `L^l D` are those of `D` (definitional). -/
theorem Lpow_carrier (l : ℕ) (D : AddCat.{v, u}) : (Lpow l D).carrier = D.carrier := rfl

/-- `L^1 D = L D` (definitional). -/
theorem Lpow_one (D : AddCat.{v, u}) : Lpow 1 D = Laurent D := rfl

namespace Lpow

/-! #### Functoriality -/

/-- The action of `Lpow.map l F` on morphisms (recursion on `l`; internal). -/
def mapHom : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}} (F : D.carrier ⥤ D'.carrier)
    [F.Additive] {X Y : Lpow l D}, (Lpow l D).Mor X Y → (Lpow l D').Mor (F.obj X) (F.obj Y)
  | 0, _, _, F, _, _, _, f => F.map f
  | l + 1, _, _, F, _, _, _, f => mapHom l (Laurent.map F) f

lemma mapHom_id : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    (F : D.carrier ⥤ D'.carrier) [F.Additive] (X : Lpow l D),
    mapHom l F (𝟙 X) = (Lpow l D').idMor (F.obj X)
  | 0, _, _, F, _, X => F.map_id X
  | l + 1, _, _, F, _, X => mapHom_id l (Laurent.map F) X

lemma mapHom_comp : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y Z : Lpow l D} (f : (Lpow l D).Mor X Y)
    (g : (Lpow l D).Mor Y Z), mapHom l F (f ≫ g) = mapHom l F f ≫ mapHom l F g
  | 0, _, _, F, _, _, _, _, f, g => F.map_comp f g
  | l + 1, _, _, F, _, _, _, _, f, g => mapHom_comp l (Laurent.map F) f g

lemma mapHom_add : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y : Lpow l D} (f g : (Lpow l D).Mor X Y),
    mapHom l F (f + g) = mapHom l F f + mapHom l F g
  | 0, _, _, F, _, _, _, _, _ => F.map_add
  | l + 1, _, _, F, _, _, _, f, g => mapHom_add l (Laurent.map F) f g

variable {D : AddCat.{v, u}} {D' : AddCat.{v', u'}} {D'' : AddCat.{v'', u''}}

/-- **`L^l F`**: the coefficientwise extension of an additive functor; `F.obj` on objects
(`Lpow.map_obj` is `rfl`), `Lpow.map 0 F = F` and `Lpow.map (l + 1) F = Lpow.map l (Laurent.map F)`
(both `rfl`). -/
@[instance_reducible]
def map (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] :
    (Lpow l D).carrier ⥤ (Lpow l D').carrier where
  obj X := F.obj X
  map f := mapHom l F f
  map_id X := mapHom_id l F X
  map_comp f g := mapHom_comp l F f g

@[simp] lemma map_obj (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] (X : Lpow l D) :
    (map l F).obj X = F.obj X := rfl

lemma map_zero_eq (F : D.carrier ⥤ D'.carrier) [F.Additive] : map 0 F = F := rfl

lemma map_succ_eq (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] :
    map (l + 1) F = map l (Laurent.map F) := rfl

instance (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] : (map l F).Additive where
  map_add {_ _ f g} := mapHom_add l F f g

/-- `Lpow.map` does not depend on the (propositional) additivity witness, and respects equality
of functors. -/
lemma map_congr (l : ℕ) {F G : D.carrier ⥤ D'.carrier} [F.Additive] [G.Additive] (h : F = G) :
    map l F = map l G := by
  subst h; rfl

/-! #### The degree-`0` inclusion -/

/-- The action of `Lpow.incl l D` on morphisms (recursion on `l`; internal). -/
def inclHom : ∀ (l : ℕ) {D : AddCat.{v, u}} {X Y : D}, D.Mor X Y → (Lpow l D).Mor X Y
  | 0, _, _, _, f => f
  | l + 1, D, _, _, f => inclHom l ((Laurent.incl D).map f)

lemma inclHom_id : ∀ (l : ℕ) {D : AddCat.{v, u}} (X : D),
    inclHom l (𝟙 X) = (Lpow l D).idMor X
  | 0, _, _ => rfl
  | l + 1, D, X => by
    change inclHom l ((Laurent.incl D).map (𝟙 X)) = _
    rw [(Laurent.incl D).map_id]
    exact inclHom_id l (D := Laurent D) X

lemma inclHom_comp : ∀ (l : ℕ) {D : AddCat.{v, u}} {X Y Z : D} (f : D.Mor X Y) (g : D.Mor Y Z),
    inclHom l (f ≫ g) = inclHom l f ≫ inclHom l g
  | 0, _, _, _, _, _, _ => rfl
  | l + 1, D, _, _, _, f, g => by
    change inclHom l ((Laurent.incl D).map (f ≫ g)) = _
    rw [(Laurent.incl D).map_comp]
    exact inclHom_comp l (D := Laurent D) _ _

lemma inclHom_add : ∀ (l : ℕ) {D : AddCat.{v, u}} {X Y : D} (f g : D.Mor X Y),
    inclHom l (f + g) = inclHom l f + inclHom l g
  | 0, _, _, _, _, _ => rfl
  | l + 1, D, _, _, f, g => by
    change inclHom l ((Laurent.incl D).map (f + g)) = _
    rw [(Laurent.incl D).map_add]
    exact inclHom_add l (D := Laurent D) _ _

variable (D) in
/-- **The degree-`0` inclusion** `ι : D ⥤ L^l D` (identity on objects, `Lpow.incl_obj` is
`rfl`). -/
@[instance_reducible]
def incl (l : ℕ) : D.carrier ⥤ (Lpow l D).carrier where
  obj X := X
  map f := inclHom l f
  map_id X := inclHom_id l X
  map_comp f g := inclHom_comp l f g

@[simp] lemma incl_obj (l : ℕ) (X : D) : (incl D l).obj X = X := rfl

lemma incl_zero_eq : incl D 0 = 𝟭 D.carrier := rfl

lemma incl_succ_map (l : ℕ) {X Y : D} (f : D.Mor X Y) :
    (incl D (l + 1)).map f = (incl (Laurent D) l).map ((Laurent.incl D).map f) := rfl

instance (l : ℕ) : (incl D l).Additive where
  map_add {_ _ f g} := inclHom_add l f g

lemma map_inclHom : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y : D} (a : D.Mor X Y),
    mapHom l F (inclHom l a) = inclHom l (F.map a)
  | 0, _, _, _, _, _, _, _ => rfl
  | l + 1, D, D', F, _, _, _, a => by
    change mapHom l (Laurent.map F) (inclHom l ((Laurent.incl D).map a)) =
      inclHom l ((Laurent.incl D').map (F.map a))
    rw [map_inclHom l (Laurent.map F), Laurent.map_incl]

/-- `L^l F` commutes with the degree-`0` inclusions. -/
lemma map_incl (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y : D} (a : D.Mor X Y) :
    (map l F).map ((incl D l).map a) = (incl D' l).map (F.map a) :=
  map_inclHom l F a

lemma naturality_aux : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    {F G : D.carrier ⥤ D'.carrier} [F.Additive] [G.Additive] (η : F ⟶ G) {X Y : Lpow l D}
    (f : (Lpow l D).Mor X Y),
    mapHom l F f ≫ inclHom l (η.app Y) = inclHom l (η.app X) ≫ mapHom l G f
  | 0, _, _, _, _, _, _, η, _, _, f => η.naturality f
  | l + 1, _, _, _, _, _, _, η, _, _, f => naturality_aux l (Laurent.mapNatTrans η) f

/-- **`L^l η`**: the degree-`0` extension of a natural transformation between additive
functors; its components are `ι (η.app X)`. -/
@[simps]
def mapNatTrans (l : ℕ) {F G : D.carrier ⥤ D'.carrier} [F.Additive] [G.Additive] (η : F ⟶ G) :
    map l F ⟶ map l G where
  app X := (incl D' l).map (η.app X)
  naturality _ _ f := naturality_aux l η f

/-- **`L^l η`** for a natural isomorphism of additive functors (degree-`0` components). -/
@[simps]
def mapNatIso (l : ℕ) {F G : D.carrier ⥤ D'.carrier} [F.Additive] [G.Additive] (η : F ≅ G) :
    map l F ≅ map l G where
  hom := mapNatTrans l η.hom
  inv := mapNatTrans l η.inv
  hom_inv_id := by
    ext X
    change (incl D' l).map (η.hom.app X) ≫ (incl D' l).map (η.inv.app X) = 𝟙 _
    rw [← Functor.map_comp, η.hom_inv_id_app]
    exact (incl D' l).map_id _
  inv_hom_id := by
    ext X
    change (incl D' l).map (η.inv.app X) ≫ (incl D' l).map (η.hom.app X) = 𝟙 _
    rw [← Functor.map_comp, η.inv_hom_id_app]
    exact (incl D' l).map_id _

/-- `L^l F` is fully faithful if `F` is. -/
def fullyFaithfulMap : ∀ (l : ℕ) {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    {F : D.carrier ⥤ D'.carrier} [F.Additive], F.FullyFaithful → (map l F).FullyFaithful
  | 0, _, _, _, _, hF => hF
  | l + 1, _, _, _, _, hF => fullyFaithfulMap l (Laurent.fullyFaithfulMap hF)

instance (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] [F.Full] [F.Faithful] :
    (map l F).Full :=
  (fullyFaithfulMap l (Functor.FullyFaithful.ofFullyFaithful F)).full

instance (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] [F.Full] [F.Faithful] :
    (map l F).Faithful :=
  (fullyFaithfulMap l (Functor.FullyFaithful.ofFullyFaithful F)).faithful

/-! #### Coefficients -/

/-- **The coefficient of the monomial `w^γ`** of a morphism of `L^l D`, `γ : Fin l → ℤ`; `γ 0`
is the exponent of the newest (innermost) variable. -/
def coeff : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y : Lpow l D} (_γ : Fin l → ℤ),
    (Lpow l D).Mor X Y →+ D.Mor X Y
  | 0, _, _, _, _ => AddMonoidHom.id _
  | _ + 1, _, _, _, γ => (Laurent.coeff (γ 0)).comp (coeff (Fin.tail γ))

lemma coeff_zero_eq {X Y : Lpow 0 D} (γ : Fin 0 → ℤ) (f : (Lpow 0 D).Mor X Y) :
    coeff γ f = f := rfl

lemma coeff_succ_eq {l : ℕ} {X Y : Lpow (l + 1) D} (γ : Fin (l + 1) → ℤ)
    (f : (Lpow (l + 1) D).Mor X Y) :
    coeff γ f = Laurent.coeff (γ 0) (coeff (D := Laurent D) (Fin.tail γ) f) := rfl

lemma coeff_cons {l : ℕ} {X Y : Lpow (l + 1) D} (n : ℤ) (α : Fin l → ℤ)
    (f : (Lpow (l + 1) D).Mor X Y) :
    coeff (Fin.cons n α : Fin (l + 1) → ℤ) f = Laurent.coeff n (coeff (D := Laurent D) α f) := by
  rw [coeff_succ_eq, Fin.tail_cons, Fin.cons_zero]

/-- Morphisms of `L^l D` are determined by their coefficients. -/
lemma ext : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y : Lpow l D} {f g : (Lpow l D).Mor X Y},
    (∀ γ, coeff γ f = coeff γ g) → f = g
  | 0, _, _, _, _, _, h => h Fin.elim0
  | l + 1, D, _, _, f, g, h => ext (D := Laurent D) fun α ↦ Laurent.ext fun n ↦ by
    have := h (Fin.cons n α)
    rwa [coeff_succ_eq, coeff_succ_eq, Fin.tail_cons, Fin.cons_zero] at this

lemma coeff_add {l : ℕ} {X Y : Lpow l D} (γ : Fin l → ℤ) (f g : (Lpow l D).Mor X Y) :
    coeff γ (f + g) = coeff γ f + coeff γ g := map_add _ _ _

lemma coeff_sub {l : ℕ} {X Y : Lpow l D} (γ : Fin l → ℤ) (f g : (Lpow l D).Mor X Y) :
    coeff γ (f - g) = coeff γ f - coeff γ g := map_sub _ _ _

lemma coeff_neg {l : ℕ} {X Y : Lpow l D} (γ : Fin l → ℤ) (f : (Lpow l D).Mor X Y) :
    coeff γ (-f) = -coeff γ f := map_neg _ _

@[simp] lemma coeff_zero {l : ℕ} {X Y : Lpow l D} (γ : Fin l → ℤ) :
    coeff γ (0 : (Lpow l D).Mor X Y) = 0 := map_zero _

lemma coeff_sum {l : ℕ} {X Y : Lpow l D} {ι : Type*} (s : Finset ι) (γ : Fin l → ℤ)
    (f : ι → (Lpow l D).Mor X Y) : coeff γ (∑ i ∈ s, f i) = ∑ i ∈ s, coeff γ (f i) :=
  map_sum _ _ _

lemma coeff_inclHom : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y : D} (γ : Fin l → ℤ) (a : D.Mor X Y),
    coeff γ (inclHom l a) = if γ = 0 then a else 0
  | 0, _, _, _, γ, a => by rw [ite_eq_left (Subsingleton.elim γ 0)]; rfl
  | l + 1, D, _, _, γ, a => by
    rw [coeff_succ_eq]
    change Laurent.coeff (γ 0) (coeff (Fin.tail γ) (inclHom l ((Laurent.incl D).map a))) = _
    rw [coeff_inclHom (D := Laurent D)]
    by_cases h : γ = 0
    · subst h
      have ht : Fin.tail (0 : Fin (l + 1) → ℤ) = 0 := rfl
      rw [ite_eq_left rfl, ite_eq_left ht]
      exact Laurent.coeff_zero_incl a
    · rw [ite_eq_right h]
      by_cases ht : Fin.tail γ = 0
      · rw [ite_eq_left ht, Laurent.coeff_incl, ite_eq_right]
        intro h0
        apply h
        rw [← Fin.cons_self_tail γ, ht, ← h0]
        exact funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
      · rw [ite_eq_right ht, map_zero]

/-- The coefficients of a degree-`0` morphism. -/
lemma coeff_incl {l : ℕ} {X Y : D} (γ : Fin l → ℤ) (a : D.Mor X Y) :
    coeff γ ((incl D l).map a) = if γ = 0 then a else 0 :=
  coeff_inclHom γ a

@[simp] lemma coeff_incl_zero {l : ℕ} {X Y : D} (a : D.Mor X Y) :
    coeff (0 : Fin l → ℤ) ((incl D l).map a) = a := by
  rw [coeff_incl, ite_eq_left rfl]

instance (l : ℕ) : (incl D l).Faithful where
  map_injective {X Y} a b h := by
    have := congrArg (coeff (D := D) (X := X) (Y := Y) (0 : Fin l → ℤ)) h
    rwa [coeff_incl_zero, coeff_incl_zero] at this

lemma coeff_id {l : ℕ} (γ : Fin l → ℤ) (X : Lpow l D) :
    coeff γ (𝟙 X) = if γ = 0 then D.idMor X else 0 := by
  have h := coeff_incl (D := D) (l := l) γ (D.idMor X)
  rw [(incl D l).map_id] at h
  exact h

lemma coeff_inclHom_comp : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y : D} {Z : Lpow l D}
    (γ : Fin l → ℤ) (a : D.Mor X Y) (f : (Lpow l D).Mor Y Z),
    coeff γ (inclHom l a ≫ f) = a ≫ coeff γ f
  | 0, _, _, _, _, _, _, _ => rfl
  | l + 1, D, _, _, _, γ, a, f => by
    rw [coeff_succ_eq, coeff_succ_eq]
    change Laurent.coeff (γ 0) (coeff (Fin.tail γ) (inclHom l ((Laurent.incl D).map a) ≫ f)) = _
    rw [coeff_inclHom_comp (D := Laurent D), Laurent.coeff_incl_comp]

lemma coeff_comp_inclHom : ∀ {l : ℕ} {D : AddCat.{v, u}} {X : Lpow l D} {Y Z : D}
    (γ : Fin l → ℤ) (f : (Lpow l D).Mor X Y) (b : D.Mor Y Z),
    coeff γ (f ≫ inclHom l b) = coeff γ f ≫ b
  | 0, _, _, _, _, _, _, _ => rfl
  | l + 1, D, _, _, _, γ, f, b => by
    rw [coeff_succ_eq, coeff_succ_eq]
    change Laurent.coeff (γ 0) (coeff (Fin.tail γ) (f ≫ inclHom l ((Laurent.incl D).map b))) = _
    rw [coeff_comp_inclHom (D := Laurent D), Laurent.coeff_comp_incl]

/-- Coefficients of `ι a ≫ f`. -/
lemma coeff_incl_comp {l : ℕ} {X Y : D} {Z : Lpow l D} (γ : Fin l → ℤ) (a : D.Mor X Y)
    (f : (Lpow l D).Mor Y Z) : coeff γ ((incl D l).map a ≫ f) = a ≫ coeff γ f :=
  coeff_inclHom_comp γ a f

/-- Coefficients of `f ≫ ι b`. -/
lemma coeff_comp_incl {l : ℕ} {X : Lpow l D} {Y Z : D} (γ : Fin l → ℤ)
    (f : (Lpow l D).Mor X Y) (b : D.Mor Y Z) : coeff γ (f ≫ (incl D l).map b) = coeff γ f ≫ b :=
  coeff_comp_inclHom γ f b

lemma coeff_mapHom : ∀ {l : ℕ} {D : AddCat.{v, u}} {D' : AddCat.{v', u'}}
    (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y : Lpow l D} (γ : Fin l → ℤ)
    (f : (Lpow l D).Mor X Y), coeff γ (mapHom l F f) = F.map (coeff γ f)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | l + 1, _, _, F, _, _, _, γ, f => by
    rw [coeff_succ_eq, coeff_succ_eq]
    change Laurent.coeff (γ 0) (coeff (Fin.tail γ) (mapHom l (Laurent.map F) f)) = _
    rw [coeff_mapHom (Laurent.map F), Laurent.coeff_map]

/-- `L^l F` acts coefficientwise. -/
lemma coeff_map {l : ℕ} (F : D.carrier ⥤ D'.carrier) [F.Additive] {X Y : Lpow l D}
    (γ : Fin l → ℤ) (f : (Lpow l D).Mor X Y) : coeff γ ((map l F).map f) = F.map (coeff γ f) :=
  coeff_mapHom F γ f

lemma map_id_map {l : ℕ} {X Y : Lpow l D} (f : (Lpow l D).Mor X Y) :
    (map l (𝟭 D.carrier)).map f = f :=
  ext fun γ ↦ by rw [coeff_map]; rfl

lemma map_comp_map {l : ℕ} (F : D.carrier ⥤ D'.carrier) [F.Additive]
    (G : D'.carrier ⥤ D''.carrier) [G.Additive] {X Y : Lpow l D} (f : (Lpow l D).Mor X Y) :
    (map l (F ⋙ G)).map f = (map l G).map ((map l F).map f) :=
  ext fun γ ↦ by rw [coeff_map, coeff_map G, coeff_map F]; rfl

variable (D) in
/-- `L^l 𝟭 ≅ 𝟭` (identity components). -/
def mapIdIso (l : ℕ) : map l (𝟭 D.carrier) ≅ 𝟭 (Lpow l D).carrier :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) fun f ↦
    (comp_id _).trans ((map_id_map f).trans (id_comp f).symm)

/-- `L^l (F ⋙ G) ≅ L^l F ⋙ L^l G` (identity components). -/
def mapCompIso (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive]
    (G : D'.carrier ⥤ D''.carrier) [G.Additive] :
    map l (F ⋙ G) ≅ map l F ⋙ map l G :=
  NatIso.ofComponents (fun X ↦ Iso.refl ((map l G).obj ((map l F).obj X))) fun f ↦
    (comp_id _).trans ((map_comp_map F G f).trans (id_comp _).symm)

/-- **Coefficients of a composite** lie in every additive submonoid containing all products of
coefficients (`coeff γ (f ≫ g)` is a finite sum of `coeff α f ≫ coeff β g`). -/
lemma coeff_comp_mem : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y Z : Lpow l D}
    (f : (Lpow l D).Mor X Y) (g : (Lpow l D).Mor Y Z) (S : AddSubmonoid (D.Mor X Z)),
    (∀ α β, coeff α f ≫ coeff β g ∈ S) → ∀ γ, coeff γ (f ≫ g) ∈ S
  | 0, _, _, _, _, f, g, S, h, γ => h γ γ
  | l + 1, D, X, _, Z, f, g, S, h, γ => by
    let S' : AddSubmonoid ((Laurent D).Mor X Z) := ⨅ n, S.comap (Laurent.coeff n)
    have hS' : coeff (Fin.tail γ) (f ≫ g) ∈ S' :=
      coeff_comp_mem (D := Laurent D) f g S' (fun α β ↦ by
        refine AddSubmonoid.mem_iInf.mpr fun n ↦ AddSubmonoid.mem_comap.mpr ?_
        refine Laurent.coeff_comp_mem _ _ S (fun i j ↦ ?_) n
        have := h (Fin.cons i α) (Fin.cons j β)
        rwa [coeff_succ_eq, coeff_succ_eq, Fin.tail_cons, Fin.tail_cons, Fin.cons_zero,
          Fin.cons_zero] at this) (Fin.tail γ)
    exact AddSubmonoid.mem_comap.mp (AddSubmonoid.mem_iInf.mp hS' (γ 0))

/-- Every morphism of `L^l D` has finitely many nonzero coefficients. -/
lemma finite_coeff_support : ∀ {l : ℕ} {D : AddCat.{v, u}} {X Y : Lpow l D}
    (f : (Lpow l D).Mor X Y), {γ | coeff γ f ≠ 0}.Finite
  | 0, _, _, _, _ => Set.toFinite _
  | l + 1, D, _, _, f => by
    have hS := finite_coeff_support (D := Laurent D) f
    let φ : (Fin (l + 1) → ℤ) → ℤ × (Fin l → ℤ) := fun γ ↦ (γ 0, Fin.tail γ)
    have hφ : Function.Injective φ := fun γ γ' h ↦ by
      rw [← Fin.cons_self_tail γ, ← Fin.cons_self_tail γ']
      simp only [φ, Prod.mk.injEq] at h
      rw [h.1, h.2]
    refine Set.Finite.of_finite_image ?_ hφ.injOn
    refine ((hS.biUnion fun α _ ↦ (Laurent.support (coeff α f)).finite_toSet).prod hS).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ' : Laurent.coeff (γ 0) (coeff (Fin.tail γ) f) ≠ 0 := hγ
    have ht : coeff (Fin.tail γ) f ≠ 0 := fun h0 ↦ hγ' (by rw [h0, map_zero])
    exact ⟨Set.mem_biUnion ht (Laurent.mem_support_iff.mpr hγ'), ht⟩

/-- **Uniform bounds on coefficients**: for a monotone family of properties of `D`-morphisms,
satisfied by `0` and with some level satisfied by each morphism, every morphism of `L^l D` has a
level satisfied by all of its coefficients. -/
lemma exists_bound_coeff {l : ℕ} {X Y : Lpow l D} (P : ℕ → D.Mor X Y → Prop)
    (mono : ∀ {b c : ℕ} {g : D.Mor X Y}, b ≤ c → P b g → P c g) (zero : ∀ b, P b 0)
    (exists_bound : ∀ g, ∃ b, P b g) (f : (Lpow l D).Mor X Y) :
    ∃ b, ∀ γ, P b (coeff γ f) := by
  choose B hB using exists_bound
  obtain ⟨s, hs⟩ := (finite_coeff_support f).exists_finset_coe
  refine ⟨s.sup fun γ ↦ B (coeff γ f), fun γ ↦ ?_⟩
  by_cases hγ : γ ∈ s
  · exact mono (Finset.le_sup (f := fun γ ↦ B (coeff γ f)) hγ) (hB _)
  · have : coeff γ f = 0 := by
      by_contra h
      exact hγ (by rw [← Finset.mem_coe, hs]; exact h)
    rw [this]
    exact zero _

/-! #### Powers of the newest variable -/

/-- The power `wⁿ` of the newest Laurent variable on `X`, in `L^{l+1} D = L^l (L D)`. -/
def w (l : ℕ) (n : ℤ) (X : Lpow (l + 1) D) : (Lpow (l + 1) D).Mor X X :=
  (incl (Laurent D) l).map (Laurent.T n X)

lemma w_zero (l : ℕ) (X : Lpow (l + 1) D) : w l 0 X = 𝟙 X :=
  (incl (Laurent D) l).map_id X

lemma w_comp_w (l : ℕ) (m n : ℤ) (X : Lpow (l + 1) D) : w l m X ≫ w l n X = w l (m + n) X := by
  rw [w, w, w, ← Functor.map_comp, Laurent.T_comp_T]

/-- `wⁿ` is central in `L^{l+1} D`. -/
lemma w_comm (l : ℕ) (n : ℤ) {X Y : Lpow (l + 1) D} (f : (Lpow (l + 1) D).Mor X Y) :
    w l n X ≫ f = f ≫ w l n Y :=
  ext (D := Laurent D) fun γ ↦ by
    rw [w, w, coeff_incl_comp, coeff_comp_incl, Laurent.T_comm]

lemma map_w (l : ℕ) (F : D.carrier ⥤ D'.carrier) [F.Additive] (n : ℤ) (X : Lpow (l + 1) D) :
    (map (l + 1) F).map (w l n X) = w l n (F.obj X) := by
  change (map l (Laurent.map F)).map ((incl (Laurent D) l).map (Laurent.T n X)) = _
  rw [map_incl, Laurent.map_T]
  rfl

variable (D) in
/-- **The old variables inside `L^{l+1} D`**: `L^l D ⥤ L^l (L D) = L^{l+1} D`, the coefficientwise
degree-`0` inclusion of the newest variable. -/
abbrev extend (l : ℕ) : (Lpow l D).carrier ⥤ (Lpow (l + 1) D).carrier :=
  map l (Laurent.incl D)

lemma extend_incl (l : ℕ) {X Y : D} (a : D.Mor X Y) :
    (extend D l).map ((incl D l).map a) = (incl D (l + 1)).map a :=
  map_incl l (Laurent.incl D) a

lemma coeff_extend {l : ℕ} {X Y : Lpow l D} (n : ℤ) (α : Fin l → ℤ)
    (f : (Lpow l D).Mor X Y) :
    coeff (Fin.cons n α : Fin (l + 1) → ℤ) ((extend D l).map f) =
      if (0 : ℤ) = n then coeff α f else 0 := by
  rw [coeff_cons, coeff_map, Laurent.coeff_incl]

/-- The images of the old variables commute with `wⁿ`. -/
lemma w_comm_extend (l : ℕ) (n : ℤ) {X Y : Lpow l D} (f : (Lpow l D).Mor X Y) :
    w l n X ≫ (extend D l).map f = (extend D l).map f ≫ w l n Y :=
  w_comm l n _

/-- `wⁿ` as an isomorphism. -/
@[simps]
def wIso (l : ℕ) (n : ℤ) (X : Lpow (l + 1) D) : X ≅ X where
  hom := w l n X
  inv := w l (-n) X
  hom_inv_id := by rw [w_comp_w, add_neg_cancel, w_zero]
  inv_hom_id := by rw [w_comp_w, neg_add_cancel, w_zero]

end Lpow

/-! ### The polynomial part `L⁺ D` -/

namespace LaurentPos

variable {D : AddCat.{v, u}}

/-- Laurent morphisms without negative coefficients. -/
def posSubgroup (X Y : Laurent D) : AddSubgroup ((Laurent D).Mor X Y) where
  carrier := {f | ∀ n < 0, Laurent.coeff n f = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' {f g} hf hg n hn := by rw [Laurent.coeff_add, hf n hn, hg n hn, add_zero]
  neg_mem' {f} hf n hn := by rw [Laurent.coeff_neg, hf n hn, neg_zero]

lemma comp_mem {X Y Z : Laurent D} {f : (Laurent D).Mor X Y} {g : (Laurent D).Mor Y Z}
    (hf : f ∈ posSubgroup X Y) (hg : g ∈ posSubgroup Y Z) : f ≫ g ∈ posSubgroup X Z := by
  intro n hn
  rw [Laurent.coeff_comp f g n _ subset_rfl]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hi : i < 0
  · rw [hf i hi, zero_comp]
  · rw [hg (n - i) (by omega), comp_zero]

lemma id_mem (X : Laurent D) : 𝟙 X ∈ posSubgroup X X := fun n hn ↦ by
  rw [Laurent.coeff_id, ite_eq_right (by omega)]

variable (D) in
/-- Type synonym carrying the `L⁺` structure during its construction (internal). -/
def Obj : Type u := D.carrier

/-- The `L⁺` category structure (internal; use `LaurentPos D`). -/
@[instance_reducible]
def categoryObj : Category.{v} (Obj D) where
  Hom (X Y : Laurent D) := posSubgroup X Y
  id (X : Laurent D) := ⟨𝟙 X, id_mem X⟩
  comp f g := ⟨f.1 ≫ g.1, comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (id_comp f.1)
  comp_id f := Subtype.ext (comp_id f.1)
  assoc f g h := Subtype.ext (assoc f.1 g.1 h.1)

attribute [local instance] categoryObj

/-- The `L⁺` preadditive structure (internal). -/
@[instance_reducible]
def preadditiveObj : Preadditive (Obj D) where
  homGroup (X Y : Laurent D) := inferInstanceAs (AddCommGroup (posSubgroup X Y))
  add_comp {X Y Z : Laurent D} (f f' : posSubgroup X Y) (g : posSubgroup Y Z) :=
    Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add {X Y Z : Laurent D} (f : posSubgroup X Y) (g g' : posSubgroup Y Z) :=
    Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

attribute [local instance] preadditiveObj

/-- The degree-`0` inclusion `D ⥤ L⁺ D` (internal). -/
@[instance_reducible]
def inclDObj : D.carrier ⥤ Obj D where
  obj X := X
  map {X Y} f := ⟨(Laurent.incl D).map f, fun n hn ↦ by
    rw [Laurent.coeff_incl, ite_eq_right (by omega)]⟩
  map_id X := Subtype.ext ((Laurent.incl D).map_id X)
  map_comp f g := Subtype.ext ((Laurent.incl D).map_comp f g)

instance : (inclDObj (D := D)).Additive where
  map_add := Subtype.ext ((Laurent.incl D).map_add)

lemma hasBinaryBiproducts_obj : HasBinaryBiproducts (Obj D) :=
  ⟨fun (X Y : D) ↦ HasBinaryBiproduct.mk
    { bicone := inclDObj.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfTotal _ <| Subtype.ext <| by
        change (Laurent.incl D).map (biprod.fst : D.Mor (X ⊞ Y) X) ≫
            (Laurent.incl D).map (biprod.inl : D.Mor X (X ⊞ Y)) +
          (Laurent.incl D).map (biprod.snd : D.Mor (X ⊞ Y) Y) ≫
            (Laurent.incl D).map (biprod.inr : D.Mor Y (X ⊞ Y)) = 𝟙 _
        rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total]
        exact (Laurent.incl D).map_id _ }⟩

open ZeroObject in
lemma hasFiniteBiproducts_obj : HasFiniteBiproducts (Obj D) := by
  have := hasBinaryBiproducts_obj (D := D)
  have : HasZeroObject (Obj D) :=
    ⟨⟨inclDObj.obj (0 : D.carrier), inclDObj.map_isZero (isZero_zero _)⟩⟩
  exact hasFiniteBiproducts_of_binary

variable (D) in
/-- The `L⁺` additive structure on `D.carrier` (internal; use `LaurentPos D`). -/
def str : AddStr.{v} D.carrier :=
  @AddStr.mk (Obj D) categoryObj preadditiveObj hasFiniteBiproducts_obj

end LaurentPos

/-- **The polynomial part `L⁺ D`** of the Laurent extension: the same objects, and the Laurent
morphisms with no negative coefficients (`blueprint/negK-high.md` §2). -/
@[instance_reducible]
def LaurentPos (D : AddCat.{v, u}) : AddCat.{v, u} := ⟨D.carrier, LaurentPos.str D⟩

namespace LaurentPos

variable {D : AddCat.{v, u}} {X Y Z : LaurentPos D}

lemma carrier_eq (D : AddCat.{v, u}) : (LaurentPos D).carrier = D.carrier := rfl

/-- The underlying Laurent morphism. -/
def toLaurent : (LaurentPos D).Mor X Y →+ (Laurent D).Mor X Y :=
  (posSubgroup (D := D) X Y).subtype

lemma toLaurent_mem (f : (LaurentPos D).Mor X Y) :
    ∀ n < 0, Laurent.coeff n (toLaurent f) = 0 :=
  (show f.1 ∈ posSubgroup (D := D) X Y from f.2)

lemma toLaurent_injective : Function.Injective (toLaurent (D := D) (X := X) (Y := Y)) :=
  Subtype.val_injective

lemma toLaurent_comp (f : (LaurentPos D).Mor X Y) (g : (LaurentPos D).Mor Y Z) :
    toLaurent (f ≫ g) = toLaurent f ≫ toLaurent g := rfl

lemma toLaurent_id (X : LaurentPos D) : toLaurent (𝟙 X) = (Laurent D).idMor X := rfl

/-- A Laurent morphism without negative coefficients, as a morphism of `L⁺ D`. -/
def ofLaurent (f : (Laurent D).Mor X Y) (hf : ∀ n < 0, Laurent.coeff n f = 0) :
    (LaurentPos D).Mor X Y :=
  ⟨f, hf⟩

@[simp] lemma toLaurent_ofLaurent (f : (Laurent D).Mor X Y)
    (hf : ∀ n < 0, Laurent.coeff n f = 0) : toLaurent (ofLaurent f hf) = f := rfl

variable (D) in
/-- **The inclusion `ι⁺ : L⁺ D ⥤ L D`** (identity on objects, faithful, additive). -/
@[instance_reducible]
def incl : (LaurentPos D).carrier ⥤ (Laurent D).carrier where
  obj X := X
  map f := toLaurent f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma incl_obj (X : LaurentPos D) : (incl D).obj X = X := rfl

lemma incl_map (f : (LaurentPos D).Mor X Y) : (incl D).map f = toLaurent f := rfl

instance : (incl D).Additive where
  map_add := rfl

instance : (incl D).Faithful where
  map_injective h := toLaurent_injective h

/-- The image of `ι⁺` has no negative coefficients. -/
lemma coeff_incl_map_neg (f : (LaurentPos D).Mor X Y) {n : ℤ} (hn : n < 0) :
    Laurent.coeff n ((incl D).map f) = 0 :=
  toLaurent_mem f n hn

variable (D) in
/-- The degree-`0` inclusion `D ⥤ L⁺ D`. -/
@[instance_reducible]
def inclD : D.carrier ⥤ (LaurentPos D).carrier := inclDObj

instance : (inclD D).Additive where
  map_add := Subtype.ext ((Laurent.incl D).map_add)

lemma inclD_comp_incl : inclD D ⋙ incl D = Laurent.incl D := rfl

/-- The monomial `wⁿ`, `n ≥ 0`, in `L⁺ D`. -/
def T (n : ℕ) (X : LaurentPos D) : (LaurentPos D).Mor X X :=
  ofLaurent (Laurent.T n X) fun m hm ↦ by
    rw [Laurent.T, Laurent.coeff_single, ite_eq_right (by omega)]

lemma incl_map_T (n : ℕ) (X : LaurentPos D) : (incl D).map (T n X) = Laurent.T n X := rfl

end LaurentPos

end

end HSFormal.LTheory
