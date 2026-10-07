import HSFormal.LTheory.Model.CZ

/-!
# Functoriality of the bounded category `C_ℤ(A)` (lower L-theory model, module 2)

`CZ.map Φ : A.cz ⟶ B.cz` applies a duality-preserving functor `Φ : A ⟶ B` entrywise; it is
strictly functorial (`map_id`, `map_comp`) and carries unitary natural isomorphisms
(`mapUnitaryIso`) and finite unitary sums (`mapIsFinSum`) to the same, componentwise diagonal.
The iterates `InvCat.czIter k A = C_ℤ(⋯ C_ℤ(A))` and `CZ.mapIter k Φ` inherit these laws.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

namespace CZ

variable {A B C : InvCat} {X Y Z : Obj A}

/-- The entrywise image of an object. -/
@[reducible]
def mapObj (Φ : A ⟶ B) (X : Obj A) : Obj B := ⟨fun v ↦ Φ.F.obj (X.obj v)⟩

/-- The entrywise image of a matrix. -/
def mapMat (Φ : A ⟶ B) (f : Mat X Y) : Mat (mapObj Φ X) (mapObj Φ Y) :=
  fun w v ↦ Φ.F.map (f w v)

lemma PropLE.mapMat (Φ : A ⟶ B) {f : Mat X Y} {b : ℕ} (hf : PropLE f b) :
    PropLE (CZ.mapMat Φ f) b := fun w v h ↦ by
  change Φ.F.map (f w v) = 0
  rw [hf w v h, Functor.map_zero]

lemma mapMat_diagMat (Φ : A ⟶ B) (d : ∀ v, X.obj v ⟶ Y.obj v) :
    mapMat Φ (diagMat d) = diagMat (Y := mapObj Φ Y) fun v ↦ Φ.F.map (d v) := by
  funext w v
  change Φ.F.map (diagMat d w v) = _
  by_cases h : v = w
  · subst h; rw [diagMat_self, diagMat_self]
  · rw [diagMat_ne _ h, diagMat_ne _ h, Functor.map_zero]

lemma mapMat_matComp (Φ : A ⟶ B) {f : Mat X Y} {b : ℕ} (hf : PropLE f b) (g : Mat Y Z) :
    mapMat Φ (matComp f g) = matComp (mapMat Φ f) (mapMat Φ g) := by
  funext u v
  change Φ.F.map (matComp f g u v) = _
  rw [matComp_eq_sum_left hf, matComp_eq_sum_left (hf.mapMat Φ), Functor.map_sum]
  exact Finset.sum_congr rfl fun w _ ↦ Φ.F.map_comp _ _

/-- The entrywise image of a morphism. -/
def mapHom (Φ : A ⟶ B) (f : X ⟶ Y) : mapObj Φ X ⟶ mapObj Φ Y :=
  ⟨mapMat Φ f.1, f.2.elim fun _ hb ↦ ⟨_, hb.mapMat Φ⟩⟩

/-- The entrywise functor `C_ℤ(A) ⥤ C_ℤ(B)`. -/
def mapFunctor (Φ : A ⟶ B) : Obj A ⥤ Obj B where
  obj := mapObj Φ
  map := mapHom Φ
  map_id X := Subtype.ext <| (mapMat_diagMat Φ _).trans <| congrArg diagMat <|
    funext fun v ↦ Φ.F.map_id (X.obj v)
  map_comp f g := Subtype.ext <| f.2.elim fun _ hb ↦ mapMat_matComp Φ hb g.1

/-- **Functoriality of `C_ℤ`**: entrywise application of `Φ`. -/
def map (Φ : A ⟶ B) : A.cz ⟶ B.cz where
  F := mapFunctor Φ
  additive := ⟨fun {_ _ _ _} ↦ Subtype.ext <| funext fun _ ↦ funext fun _ ↦ Φ.F.map_add⟩
  map_star _ := Subtype.ext <| funext fun _ ↦ funext fun _ ↦ Φ.map_star _

@[simp] lemma map_obj_obj (Φ : A ⟶ B) (X : A.cz) (v : ℤ) :
    ((map Φ).F.obj X).obj v = Φ.F.obj (X.obj v) := rfl

@[simp] lemma map_map_apply (Φ : A ⟶ B) {X Y : A.cz} (f : X ⟶ Y) (w v : ℤ) :
    ((map Φ).F.map f).1 w v = Φ.F.map (f.1 w v) := rfl

lemma map_diag (Φ : A ⟶ B) {X Y : A.cz} (d : ∀ v, X.obj v ⟶ Y.obj v) :
    (map Φ).F.map (diag d) = diag (Y := (map Φ).F.obj Y) fun v ↦ Φ.F.map (d v) :=
  Subtype.ext (mapMat_diagMat Φ d)

lemma map_id (A : InvCat) : map (𝟙 A) = 𝟙 A.cz := rfl

lemma map_comp (Φ : A ⟶ B) (Ψ : B ⟶ C) : map (Φ ≫ Ψ) = map Φ ≫ map Ψ := rfl

/-- Unitary natural isomorphisms are carried entrywise. -/
@[simps! iso_hom_app iso_inv_app]
def mapUnitaryIso {Φ Ψ : A ⟶ B} (e : InvCat.UnitaryIso Φ Ψ) :
    InvCat.UnitaryIso (map Φ) (map Ψ) where
  iso := NatIso.ofComponents
    (fun X ↦ diagIso (X := (map Φ).F.obj X) (Y := (map Ψ).F.obj X) fun v ↦ e.iso.app (X.obj v))
    fun {X Y} f ↦ by
      ext u v
      erw [diagIso_hom, diagIso_hom, comp_diag_apply, diag_comp_apply, map_map_apply,
        map_map_apply]
      exact e.iso.hom.naturality (f.1 u v)
  star_hom X := (star_diag _).trans (diag_ext fun v ↦ e.star_hom (X.obj v))

/-- The entrywise inclusion of a summand `Φ i` of `S`. -/
@[simps]
def mapInc {Φ S : A ⟶ B} (ι : Φ.F ⟶ S.F) : (map Φ).F ⟶ (map S).F where
  app X := diag (X := (map Φ).F.obj X) (Y := (map S).F.obj X) fun v ↦ ι.app (X.obj v)
  naturality X Y f := by
    ext u v
    erw [comp_diag_apply, diag_comp_apply, map_map_apply, map_map_apply]
    exact ι.naturality (f.1 u v)

/-- Finite unitary sums are carried entrywise. -/
@[simps inc]
def mapIsFinSum {ι : Type*} [Fintype ι] {Φ : ι → (A ⟶ B)} {S : A ⟶ B}
    (h : InvCat.IsFinSum Φ S) : InvCat.IsFinSum (fun i ↦ map (Φ i)) (map S) where
  inc i := mapInc (h.inc i)
  inc_star_self i X := by
    erw [mapInc_app, star_diag, diag_comp_diag, ← diag_id]
    exact diag_ext fun v ↦ h.inc_star_self i (X.obj v)
  inc_star_ne i j hij X := by
    erw [mapInc_app, mapInc_app, star_diag, diag_comp_diag, ← diag_zero]
    exact diag_ext fun v ↦ h.inc_star_ne i j hij (X.obj v)
  total X := by
    simp only [mapInc_app]
    calc _ = ∑ i, diag (X := (map S).F.obj X) (Y := (map S).F.obj X)
            (fun v ↦ B.inv.star ((h.inc i).app (X.obj v)) ≫ (h.inc i).app (X.obj v)) :=
          Finset.sum_congr rfl fun i _ ↦ by erw [star_diag, diag_comp_diag]; rfl
      _ = 𝟙 _ := by
          rw [← diag_sum, ← diag_id]
          exact diag_ext fun v ↦ h.total (X.obj v)

end CZ

/-- `C_ℤ^{∘k}(A)`: the iterated bounded categories of the colimit model. -/
def InvCat.czIter : ℕ → InvCat → InvCat
  | 0, A => A
  | k + 1, A => (InvCat.czIter k A).cz

@[simp] lemma InvCat.czIter_zero (A : InvCat) : A.czIter 0 = A := rfl

@[simp] lemma InvCat.czIter_succ (k : ℕ) (A : InvCat) : A.czIter (k + 1) = (A.czIter k).cz :=
  rfl

namespace CZ

variable {A B C : InvCat}

/-- Functoriality of the iterates. -/
def mapIter : ∀ (k : ℕ) {A B : InvCat}, (A ⟶ B) → (A.czIter k ⟶ B.czIter k)
  | 0, _, _, Φ => Φ
  | k + 1, _, _, Φ => map (mapIter k Φ)

lemma mapIter_zero (Φ : A ⟶ B) : mapIter 0 Φ = Φ := rfl

lemma mapIter_succ (k : ℕ) (Φ : A ⟶ B) : mapIter (k + 1) Φ = map (mapIter k Φ) := rfl

lemma mapIter_id : ∀ (k : ℕ) (A : InvCat), mapIter k (𝟙 A) = 𝟙 (A.czIter k)
  | 0, _ => rfl
  | k + 1, A => by rw [mapIter_succ, mapIter_id k A]; exact map_id _

lemma mapIter_comp : ∀ (k : ℕ) (Φ : A ⟶ B) (Ψ : B ⟶ C),
    mapIter k (Φ ≫ Ψ) = mapIter k Φ ≫ mapIter k Ψ
  | 0, _, _ => rfl
  | k + 1, Φ, Ψ => by rw [mapIter_succ, mapIter_comp k Φ Ψ]; exact map_comp _ _

/-- Unitary natural isomorphisms are carried to the iterates. -/
def mapIterUnitaryIso : ∀ (k : ℕ) {Φ Ψ : A ⟶ B}, InvCat.UnitaryIso Φ Ψ →
    InvCat.UnitaryIso (mapIter k Φ) (mapIter k Ψ)
  | 0, _, _, e => e
  | k + 1, _, _, e => mapUnitaryIso (mapIterUnitaryIso k e)

/-- Finite unitary sums are carried to the iterates. -/
def mapIterIsFinSum {ι : Type*} [Fintype ι] : ∀ (k : ℕ) {Φ : ι → (A ⟶ B)} {S : A ⟶ B},
    InvCat.IsFinSum Φ S → InvCat.IsFinSum (fun i ↦ mapIter k (Φ i)) (mapIter k S)
  | 0, _, _, h => h
  | k + 1, _, _, h => mapIsFinSum (mapIterIsFinSum k h)

end CZ

end

end HSFormal.LTheory
