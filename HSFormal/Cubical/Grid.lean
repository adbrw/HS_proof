import HSFormal.Cubical.DualBridge

/-!
# Cubical grids: tori, cube pairs and `W = Tⁿ ⊗ CPcell` (cubical module C4)

Iterated tensor products `prodComplex n C` of `1`-dimensional complexes carry iterated tensor
products of `1`-dimensional dualities (`HtpyEquiv.dualProd`, `SymDuality.prod`), with the Koszul
isomorphism at each step and the dimension cast `1 + n = n + 1`.

* `torus.duality m n : SymDuality (torus m n) n _`, the closed symmetric duality of
  `Tⁿ = C_m^{⊗n}` (design §2.3): `φ = ⊗ (φ₀ + Tφ₀)/2`, explicit inverse `b = Θ (⊗ φ₀⁻¹)`
  (monomial), and the explicit tensor homotopies.  `φ` and `b` are cell-local
  (`torus.isCellLocal_duality`, `torus.isCellLocal_inv`); metric radii are in `GridSeam`.
* `torus.z`, the product fundamental cycle, with `ε ∘ φ = ⟨-, z⟩` (`torus.aug_duality`).
* `cube.relDuality`, `cube.absDuality`: the cube pair `(Iⁿ, ∂Iⁿ)` in tensor form
  `cubeRel m n = C(I, ∂I)^{⊗n}`, with both pair maps (relative cochains to absolute chains and
  conversely) as tensor products of the interval pair dualities.
* `torusCP m n = Tⁿ ⊗ CPcell` (the `W_i` of §8/§11) with `torusCP.duality` of dimension `n + 4`
  and its M1 Poincaré complex `torusCP.symPoincare`.
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C C' D D' E : BasedComplex} {N N' M : ℕ}

/-! ### Homotopy bookkeeping -/

@[simp] theorem Htpy.trans_h {f g k : Hom C D} (H : Htpy f g) (H' : Htpy g k) :
    (H.trans H').h = H.h + H'.h := rfl

@[simp] theorem Htpy.symm_h {f g : Hom C D} (H : Htpy f g) : H.symm.h = -H.h := rfl

@[simp] theorem Htpy.compLeft_h {f g : Hom C D} (p : Hom D D') (H : Htpy f g) :
    (H.compLeft p).h = p.f * H.h := rfl

@[simp] theorem Htpy.compRight_h {f g : Hom C D} (H : Htpy f g) (p : Hom C' C) :
    (H.compRight p).h = H.h * p.f := rfl

@[simp] theorem Htpy.congr_h {f g f' g' : Hom C D} (H : Htpy f g) (hf : f = f') (hg : g = g') :
    (H.congr hf hg).h = H.h := by
  subst hf hg; rfl

@[simp] theorem Htpy.ofEq_h {f g : Hom C D} (h : f = g) : (Htpy.ofEq h).h = 0 := by
  subst h; rfl

@[simp] theorem Htpy.tensorRight_h {f f' : Hom C C'} (H : Htpy f f') (g : Hom D D') :
    (H.tensorRight g).h = H.h ⊗ₖ g.f := rfl

@[simp] theorem Htpy.tensorLeft_h (f : Hom C C') {g g' : Hom D D'} (H : Htpy g g') :
    (Htpy.tensorLeft f H).h = (f.f * C.sgn) ⊗ₖ H.h := rfl

theorem HtpyEquiv.trans_homInv_h (e : HtpyEquiv C D) (e' : HtpyEquiv D D') :
    (e.trans e').homInv.h = e.inv.f * (e'.homInv.h * e.hom.f) + e.homInv.h := by
  simp [HtpyEquiv.trans]

theorem HtpyEquiv.trans_invHom_h (e : HtpyEquiv C D) (e' : HtpyEquiv D D') :
    (e.trans e').invHom.h = e'.hom.f * (e.invHom.h * e'.inv.f) + e'.invHom.h := by
  simp [HtpyEquiv.trans]

theorem HtpyEquiv.tensor_homInv_h (e : HtpyEquiv C C') (e' : HtpyEquiv D D') :
    (e.tensor e').homInv.h =
      e.homInv.h ⊗ₖ (e'.inv.f * e'.hom.f) + C.sgn ⊗ₖ e'.homInv.h := by
  simp [HtpyEquiv.tensor]

theorem HtpyEquiv.tensor_invHom_h (e : HtpyEquiv C C') (e' : HtpyEquiv D D') :
    (e.tensor e').invHom.h =
      e.invHom.h ⊗ₖ (e'.hom.f * e'.inv.f) + C'.sgn ⊗ₖ e'.invHom.h := by
  simp [HtpyEquiv.tensor]

/-! ### Iterated tensor products -/

theorem dimLE_point : point.DimLE 0 := fun _ ↦ le_rfl

/-- An iterated tensor product of complexes of dimension `≤ 1` has dimension `≤ n`. -/
theorem DimLE.prod : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, (C i).DimLE 1) →
    (prodComplex n C).DimLE n
  | 0, _, _ => dimLE_point
  | n + 1, _, h => fun p ↦ by
    have h₀ := h 0 p.1
    have h₁ := DimLE.prod n (fun i ↦ h i.succ) p.2
    change _ + _ ≤ n + 1
    omega

/-! ### The point -/

/-- The point is self-dual in dimension `0`, by the identity. -/
def point.dualHom : Hom (point.dual 0 dimLE_point) point where
  f := 1
  deg0 _ _ _ := rfl
  comm := by simp [point]

/-- The `0`-dimensional symmetric duality of the point. -/
def point.duality : SymDuality point 0 dimLE_point where
  toHtpyEquiv := HtpyEquiv.ofIso point.dualHom 1 (fun _ _ _ ↦ rfl) (by simp [point.dualHom])
    (by simp [point.dualHom])
  symm := by ext ⟨⟩ ⟨⟩; simp [transpose_f, eps, HtpyEquiv.ofIso, point.dualHom, point]

@[simp] theorem point.duality_hom_f : point.duality.hom.f = 1 := rfl
@[simp] theorem point.duality_inv_f : point.duality.inv.f = 1 := rfl
@[simp] theorem point.duality_homInv_h : point.duality.homInv.h = 0 := Htpy.ofEq_h _
@[simp] theorem point.duality_invHom_h : point.duality.invHom.h = 0 := Htpy.ofEq_h _

/-! ### Dimension casts -/

/-- Transport a duality equivalence `C^{N-*} ≃ D` along `N = N'`. -/
def HtpyEquiv.castDim {hN : C.DimLE N} (e : HtpyEquiv (C.dual N hN) D) (h : N = N')
    (hN' : C.DimLE N') : HtpyEquiv (C.dual N' hN') D := by
  subst h; exact e

section CastDim

variable {hN : C.DimLE N} (e : HtpyEquiv (C.dual N hN) D) (h : N = N') (hN' : C.DimLE N')

@[simp] theorem HtpyEquiv.castDim_hom_f : (e.castDim h hN').hom.f = e.hom.f := by subst h; rfl
@[simp] theorem HtpyEquiv.castDim_inv_f : (e.castDim h hN').inv.f = e.inv.f := by subst h; rfl
@[simp] theorem HtpyEquiv.castDim_homInv_h : (e.castDim h hN').homInv.h = e.homInv.h := by
  subst h; rfl
@[simp] theorem HtpyEquiv.castDim_invHom_h : (e.castDim h hN').invHom.h = e.invHom.h := by
  subst h; rfl

end CastDim

/-- Transport a symmetric duality along `N = N'`. -/
def SymDuality.castDim {hN : C.DimLE N} (P : SymDuality C N hN) (h : N = N')
    (hN' : C.DimLE N') : SymDuality C N' hN' := by
  subst h; exact P

theorem SymDuality.castDim_toHtpyEquiv {hN : C.DimLE N} (P : SymDuality C N hN) (h : N = N')
    (hN' : C.DimLE N') : (P.castDim h hN').toHtpyEquiv = P.toHtpyEquiv.castDim h hN' := by
  subst h; rfl

@[simp] theorem SymDuality.castDim_hom_f {hN : C.DimLE N} (P : SymDuality C N hN) (h : N = N')
    (hN' : C.DimLE N') : (P.castDim h hN').hom.f = P.hom.f := by subst h; rfl

@[simp] theorem SymDuality.castDim_inv_f {hN : C.DimLE N} (P : SymDuality C N hN) (h : N = N')
    (hN' : C.DimLE N') : (P.castDim h hN').inv.f = P.inv.f := by subst h; rfl

/-! ### Tensor products of duality equivalences -/

/-- The tensor product of duality equivalences `C^{N-*} ≃ D` and `C'^{M-*} ≃ D'`, through the
Koszul isomorphism `(C ⊗ C')^{N+M-*} ≅ C^{N-*} ⊗ C'^{M-*}` (as in `SymDuality.tensor`). -/
def HtpyEquiv.dualTensor {hC : C.DimLE N} {hC' : C'.DimLE M} (e : HtpyEquiv (C.dual N hC) D)
    (e' : HtpyEquiv (C'.dual M hC') D') :
    HtpyEquiv ((C.tensor C').dual (N + M) (hC.tensor hC')) (D.tensor D') :=
  (dualTensorEquiv hC hC').trans (e.tensor e')

section DualTensor

variable {hC : C.DimLE N} {hC' : C'.DimLE M} (e : HtpyEquiv (C.dual N hC) D)
  (e' : HtpyEquiv (C'.dual M hC') D')

theorem HtpyEquiv.dualTensor_hom_f :
    (e.dualTensor e').hom.f = (e.hom.f ⊗ₖ e'.hom.f) * koszul C C' M := rfl

theorem HtpyEquiv.dualTensor_inv_f :
    (e.dualTensor e').inv.f = koszul C C' M * (e.inv.f ⊗ₖ e'.inv.f) := rfl

theorem HtpyEquiv.dualTensor_homInv_h :
    (e.dualTensor e').homInv.h = koszul C C' M *
      ((e.homInv.h ⊗ₖ (e'.inv.f * e'.hom.f) + (C.dual N hC).sgn ⊗ₖ e'.homInv.h) *
        koszul C C' M) := by
  rw [HtpyEquiv.dualTensor, HtpyEquiv.trans_homInv_h, HtpyEquiv.tensor_homInv_h]
  simp [dualTensorEquiv, tensorDual]
  erw [Htpy.ofEq_h, add_zero]
  rfl

theorem HtpyEquiv.dualTensor_invHom_h :
    (e.dualTensor e').invHom.h =
      e.invHom.h ⊗ₖ (e'.hom.f * e'.inv.f) + D.sgn ⊗ₖ e'.invHom.h := by
  rw [HtpyEquiv.dualTensor, HtpyEquiv.trans_invHom_h, HtpyEquiv.tensor_invHom_h]
  simp [dualTensorEquiv]

theorem SymDuality.tensor_toHtpyEquiv {P : SymDuality C N hC} {Q : SymDuality C' M hC'} :
    (P.tensor Q).toHtpyEquiv = P.toHtpyEquiv.dualTensor Q.toHtpyEquiv := rfl

end DualTensor

/-- The iterated tensor product of `1`-dimensional duality equivalences `(C i)^{1-*} ≃ D i`:
an `n`-dimensional duality equivalence `(⊗ C i)^{n-*} ≃ ⊗ D i`. -/
def HtpyEquiv.dualProd : (n : ℕ) → {C D : Fin n → BasedComplex} → (hC : ∀ i, (C i).DimLE 1) →
    (∀ i, HtpyEquiv ((C i).dual 1 (hC i)) (D i)) →
    HtpyEquiv ((prodComplex n C).dual n (DimLE.prod n hC)) (prodComplex n D)
  | 0, _, _, _, _ => point.duality.toHtpyEquiv
  | n + 1, _, _, hC, e => ((e 0).dualTensor (HtpyEquiv.dualProd n (fun i ↦ hC i.succ)
      fun i ↦ e i.succ)).castDim (Nat.add_comm 1 n) _

/-- The iterated tensor product of `1`-dimensional symmetric dualities. -/
def SymDuality.prod : (n : ℕ) → {C : Fin n → BasedComplex} → (hC : ∀ i, (C i).DimLE 1) →
    (∀ i, SymDuality (C i) 1 (hC i)) → SymDuality (prodComplex n C) n (DimLE.prod n hC)
  | 0, _, _, _ => point.duality
  | n + 1, _, hC, P => ((P 0).tensor (SymDuality.prod n (fun i ↦ hC i.succ)
      fun i ↦ P i.succ)).castDim (Nat.add_comm 1 n) _

theorem SymDuality.prod_toHtpyEquiv : (n : ℕ) → {C : Fin n → BasedComplex} →
    (hC : ∀ i, (C i).DimLE 1) → (P : ∀ i, SymDuality (C i) 1 (hC i)) →
    (SymDuality.prod n hC P).toHtpyEquiv = HtpyEquiv.dualProd n hC fun i ↦ (P i).toHtpyEquiv
  | 0, _, _, _ => rfl
  | n + 1, _, hC, P => by
    rw [SymDuality.prod, SymDuality.castDim_toHtpyEquiv, SymDuality.tensor_toHtpyEquiv,
      SymDuality.prod_toHtpyEquiv n]
    rfl

theorem HtpyEquiv.dualProd_succ {n : ℕ} {C D : Fin (n + 1) → BasedComplex}
    (hC : ∀ i, (C i).DimLE 1) (e : ∀ i, HtpyEquiv ((C i).dual 1 (hC i)) (D i)) :
    HtpyEquiv.dualProd (n + 1) hC e = ((e 0).dualTensor (HtpyEquiv.dualProd n (fun i ↦ hC i.succ)
      fun i ↦ e i.succ)).castDim (Nat.add_comm 1 n) _ := rfl

/-- The iterated tensor product of chain maps. -/
def Hom.prod : (n : ℕ) → {C D : Fin n → BasedComplex} → (∀ i, Hom (C i) (D i)) →
    Hom (prodComplex n C) (prodComplex n D)
  | 0, _, _, _ => Hom.id point
  | n + 1, _, _, f => (f 0).tensor (Hom.prod n fun i ↦ f i.succ)

/-! ### Fundamental cycles -/

/-- The product `⊗ z i` of chains of the factors. -/
def prodCycle : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, (C i).X → ℚ) →
    (prodComplex n C).X → ℚ
  | 0, _, _ => fun _ ↦ 1
  | n + 1, _, z => fun p ↦ z 0 p.1 * prodCycle n (fun i ↦ z i.succ) p.2

theorem IsCycle.castDim {z : C.X → ℚ} (hz : IsCycle C N z) (h : N = N') : IsCycle C N' z :=
  h ▸ hz

theorem isCycle_point : IsCycle point 0 fun _ ↦ 1 := ⟨fun _ _ ↦ rfl, by simp [point]⟩

/-- The product of `1`-cycles is an `n`-cycle (the product fundamental cycle). -/
theorem IsCycle.prod : (n : ℕ) → {C : Fin n → BasedComplex} → {z : ∀ i, (C i).X → ℚ} →
    (∀ i, IsCycle (C i) 1 (z i)) → IsCycle (prodComplex n C) n (prodCycle n z)
  | 0, _, _, _ => isCycle_point
  | n + 1, _, _, h => ((h 0).tensor (IsCycle.prod n fun i ↦ h i.succ)).castDim (Nat.add_comm 1 n)

/-- `ε ∘ φ = ⟨-, ⊗ z i⟩` for the product duality, when it holds for each factor. -/
theorem SymDuality.aug_prod : (n : ℕ) → {C : Fin n → BasedComplex} →
    {hC : ∀ i, (C i).DimLE 1} → {P : ∀ i, SymDuality (C i) 1 (hC i)} →
    {z : ∀ i, (C i).X → ℚ} → (∀ i, IsCycle (C i) 1 (z i)) →
    (∀ i τ, ∑ σ, (C i).aug σ * (P i).hom.f σ τ = z i τ) → ∀ τ,
    ∑ σ, (prodComplex n C).aug σ * (SymDuality.prod n hC P).hom.f σ τ = prodCycle n z τ
  | 0, _, _, _, _, _, _ => fun τ ↦ by
    change ∑ σ : Unit, (if (0 : ℕ) = 0 then (1 : ℚ) else 0) * (1 : Matrix Unit Unit ℚ) σ τ = 1
    cases τ
    simp
  | n + 1, _, _, P, _, hz, hP => fun τ ↦ by
    rw [SymDuality.prod, SymDuality.castDim_hom_f]
    exact SymDuality.aug_tensor _ _ (hz 0) (IsCycle.prod n fun i ↦ hz i.succ) (hP 0)
      (SymDuality.aug_prod n (fun i ↦ hz i.succ) fun i ↦ hP i.succ) τ

/-! ### Cell-locality of product dualities -/

theorem isCellLocal_one : IsCellLocal (C := C) 1 := fun σ τ h ↦
  ⟨σ, fun _ _ hσ ↦ ⟨hσ, by rwa [← show σ = τ from by_contra fun h' ↦ h (one_apply_ne h')]⟩⟩

theorem isCellLocal_koszul_mul {u : Matrix (C.X × D.X) (C.X × D.X) ℚ}
    (hu : IsCellLocal (C := C.tensor D) u) : IsCellLocal (C := C.tensor D) (koszul C D M * u) :=
  hu.diagonal_mul _

theorem SymDuality.isCellLocal_prod_hom : (n : ℕ) → {C : Fin n → BasedComplex} →
    {hC : ∀ i, (C i).DimLE 1} → {P : ∀ i, SymDuality (C i) 1 (hC i)} →
    (∀ i, IsCellLocal (C := C i) (P i).hom.f) →
    IsCellLocal (C := prodComplex n C) (SymDuality.prod n hC P).hom.f
  | 0, _, _, _, _ => isCellLocal_one
  | n + 1, _, _, _, h => by
    rw [SymDuality.prod, SymDuality.castDim_hom_f]
    exact IsCellLocal.tensor_hom (h 0) (SymDuality.isCellLocal_prod_hom n fun i ↦ h i.succ)

theorem SymDuality.isCellLocal_prod_inv : (n : ℕ) → {C : Fin n → BasedComplex} →
    {hC : ∀ i, (C i).DimLE 1} → {P : ∀ i, SymDuality (C i) 1 (hC i)} →
    (∀ i, IsCellLocal (C := C i) (P i).inv.f) →
    IsCellLocal (C := prodComplex n C) (SymDuality.prod n hC P).inv.f
  | 0, _, _, _, _ => isCellLocal_one
  | n + 1, _, _, _, h => by
    rw [SymDuality.prod, SymDuality.castDim_inv_f]
    exact isCellLocal_koszul_mul
      ((h 0).kronecker (SymDuality.isCellLocal_prod_inv n fun i ↦ h i.succ))

/-! ### The circle -/

section Circle

variable (m : ℕ) [NeZero m]

theorem circle.ne_add_one (hm : 2 ≤ m) (e : Fin m) : e ≠ e + 1 := fun h ↦ by
  have h₁ : (0 : Fin m) = 1 := by simpa using congrArg (· - e) h
  have := congrArg Fin.val h₁
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The circle inverse `b = φ₀⁻¹` is cell-local: `b v_k = e_k^*`, `b e_k = v_{k+1}^*`. -/
theorem circle.isCellLocal_inv (hm : 2 ≤ m) :
    IsCellLocal (C := circle m) (circle.duality m).inv.f := by
  intro σ τ h
  rw [circle.duality_inv_f] at h
  rcases σ with v | e <;> rcases τ with w | f <;> simp [circle.bMat] at h
  · subst h
    refine ⟨.inr f, fun Q hQ hf ↦ ⟨hQ _ _ ?_ hf, hf⟩⟩
    simp [(circle.ne_add_one m hm f).symm]
  · subst h
    refine ⟨.inr e, fun Q hQ he ↦ ⟨he, hQ _ _ ?_ he⟩⟩
    simp [circle.ne_add_one m hm e]

theorem circle.duality_homInv_h :
    (circle.duality m).homInv.h =
      circle.bMat m * -((1 / 2 : ℚ) • (oneDim.flip (circle.isCycle_z m)).h) := by
  simp [circle.duality, SymDuality.ofFlip, HtpyEquiv.ofHtpy, Htpy.toSym, circle.capEquiv,
    HtpyEquiv.ofIso, Hom.ofInverse]
  exact Htpy.ofEq_h _

theorem circle.duality_invHom_h :
    (circle.duality m).invHom.h =
      -((1 / 2 : ℚ) • (oneDim.flip (circle.isCycle_z m)).h) * circle.bMat m := by
  simp [circle.duality, SymDuality.ofFlip, HtpyEquiv.ofHtpy, Htpy.toSym, circle.capEquiv,
    HtpyEquiv.ofIso, Hom.ofInverse]
  exact Htpy.ofEq_h _

end Circle

/-! ### The torus `Tⁿ = C_m^{⊗n}` -/

section Torus

variable (m n : ℕ) [NeZero m]

theorem torus.dimLE : (torus m n).DimLE n := DimLE.prod n fun _ ↦ dimLE_oneDim

/-- **The closed symmetric duality of `Tⁿ`**: `φ = Θ (⊗ (φ₀ + Tφ₀)/2)` with the monomial inverse
`b = Θ (⊗ φ₀⁻¹)` and the tensor homotopies (design §2.3, F9–F10). -/
def torus.duality : SymDuality (torus m n) n (torus.dimLE m n) :=
  SymDuality.prod n _ fun _ ↦ circle.duality m

theorem torus.duality_succ_hom_f : (torus.duality m (n + 1)).hom.f =
    ((circle.duality m).hom.f ⊗ₖ (torus.duality m n).hom.f) * koszul (circle m) (torus m n) n := by
  rw [torus.duality, SymDuality.prod, SymDuality.castDim_hom_f]; rfl

theorem torus.duality_succ_inv_f : (torus.duality m (n + 1)).inv.f =
    koszul (circle m) (torus m n) n * (circle.bMat m ⊗ₖ (torus.duality m n).inv.f) := by
  rw [torus.duality, SymDuality.prod, SymDuality.castDim_inv_f]; rfl

theorem torus.duality_succ_homInv_h : (torus.duality m (n + 1)).homInv.h =
    koszul (circle m) (torus m n) n * (((circle.duality m).homInv.h ⊗ₖ
      ((torus.duality m n).inv.f * (torus.duality m n).hom.f) +
        ((circle m).dual 1 dimLE_oneDim).sgn ⊗ₖ (torus.duality m n).homInv.h) *
          koszul (circle m) (torus m n) n) := by
  rw [torus.duality, SymDuality.prod, SymDuality.castDim_toHtpyEquiv,
    HtpyEquiv.castDim_homInv_h, SymDuality.tensor_toHtpyEquiv, HtpyEquiv.dualTensor_homInv_h]
  rfl

theorem torus.duality_succ_invHom_h : (torus.duality m (n + 1)).invHom.h =
    (circle.duality m).invHom.h ⊗ₖ ((torus.duality m n).hom.f * (torus.duality m n).inv.f) +
      (circle m).sgn ⊗ₖ (torus.duality m n).invHom.h := by
  rw [torus.duality, SymDuality.prod, SymDuality.castDim_toHtpyEquiv,
    HtpyEquiv.castDim_invHom_h, SymDuality.tensor_toHtpyEquiv, HtpyEquiv.dualTensor_invHom_h]
  rfl

/-- For `m ≥ 2`, `φ` is cell-local: each entry lies over a single cell (radius `0`). -/
theorem torus.isCellLocal_duality (hm : 2 ≤ m) :
    IsCellLocal (C := torus m n) (torus.duality m n).hom.f :=
  SymDuality.isCellLocal_prod_hom n fun _ ↦ circle.isCellLocal_duality m hm

/-- For `m ≥ 2`, the inverse `b` is cell-local. -/
theorem torus.isCellLocal_inv (hm : 2 ≤ m) :
    IsCellLocal (C := torus m n) (torus.duality m n).inv.f :=
  SymDuality.isCellLocal_prod_inv n fun _ ↦ circle.isCellLocal_inv m hm

/-- The fundamental cycle `z = ⊗ Σ e` of `Tⁿ`; all its coefficients are `1`. -/
def torus.z : (torus m n).X → ℚ := prodCycle n fun _ ↦ circle.z m

theorem torus.isCycle_z : IsCycle (torus m n) n (torus.z m n) :=
  IsCycle.prod n fun _ ↦ circle.isCycle_z m

/-- `ε ∘ φ = ⟨-, z⟩` on `Tⁿ`. -/
theorem torus.aug_duality (τ : (torus m n).X) :
    ∑ σ, (torus m n).aug σ * (torus.duality m n).hom.f σ τ = torus.z m n τ :=
  SymDuality.aug_prod n (fun _ ↦ circle.isCycle_z m) (fun _ ↦ circle.aug_duality m) τ

end Torus

/-! ### Cube pairs `(Iⁿ, ∂Iⁿ)` -/

section Cube

variable (m n : ℕ)

/-- The relative complex `C(Iⁿ, ∂Iⁿ) = C(I, ∂I)^{⊗n}` of the cube `I_{m+1}^{⊗n}`. -/
abbrev cubeRel : BasedComplex := prodComplex n fun _ ↦ interval.rel m

theorem cube.dimLE (m : ℕ) : (cube m n).DimLE n := DimLE.prod n fun _ ↦ dimLE_oneDim

theorem cubeRel.dimLE : (cubeRel m n).DimLE n := DimLE.prod n fun _ ↦ interval.dimLE_rel m

/-- The projection `C(Iⁿ) → C(Iⁿ, ∂Iⁿ)`, the tensor product of the interval projections. -/
def cube.proj : Hom (cube (m + 1) n) (cubeRel m n) :=
  Hom.prod n fun _ ↦ projHom (interval.isSub_isEnd m)

/-- **Cube pair duality, relative cochains to chains**: `C^{n-*}(Iⁿ, ∂Iⁿ) ≃ C(Iⁿ)`, the tensor
product of the interval relative caps `F` (inverse `⊗ e₀^* ε`, explicit homotopies). -/
def cube.relDuality : HtpyEquiv ((cubeRel m n).dual n (cubeRel.dimLE m n)) (cube (m + 1) n) :=
  HtpyEquiv.dualProd n _ fun _ ↦ interval.relDuality m

/-- **Cube pair duality, cochains to relative chains**: `C^{n-*}(Iⁿ) ≃ C(Iⁿ, ∂Iⁿ)`, the tensor
product of the transposed interval pair maps. -/
def cube.absDuality : HtpyEquiv ((cube (m + 1) n).dual n (cube.dimLE n (m + 1))) (cubeRel m n) :=
  HtpyEquiv.dualProd n _ fun _ ↦ interval.absDuality m

end Cube

/-! ### `W = Tⁿ ⊗ CPcell` -/

section TorusCP

variable (m n : ℕ) [NeZero m]

/-- The chain model `W = Tⁿ ⊗ CPcell` of §8/§11 (design §0); control ignores the `CP²` factor. -/
abbrev torusCP : BasedComplex := (torus m n).tensor CPcell

theorem torusCP.dimLE : (torusCP m n).DimLE (n + 4) := (torus.dimLE m n).tensor CPcell.dimLE

/-- The `(n + 4)`-dimensional symmetric duality `φ_W = (φ_T ⊗ φ_CP) Θ` of `W`. -/
def torusCP.duality : SymDuality (torusCP m n) (n + 4) (torusCP.dimLE m n) :=
  (torus.duality m n).tensor CPcell.duality

/-- The fundamental cycle `z_W = z_T ⊗ e₄`. -/
def torusCP.z : (torusCP m n).X → ℚ := fun p ↦ torus.z m n p.1 * CPcell.z p.2

theorem torusCP.isCycle_z : IsCycle (torusCP m n) (n + 4) (torusCP.z m n) :=
  (torus.isCycle_z m n).tensor CPcell.isCycle_z

/-- `ε ∘ φ_W = ⟨-, z_W⟩` (the degree-0 augmentation of (8.6)). -/
theorem torusCP.aug_duality (τ : (torusCP m n).X) :
    ∑ σ, (torusCP m n).aug σ * (torusCP.duality m n).hom.f σ τ = torusCP.z m n τ :=
  SymDuality.aug_tensor _ _ (torus.isCycle_z m n) CPcell.isCycle_z (torus.aug_duality m n)
    CPcell.aug_φ τ

/-- Pullbacks of subcomplexes of `Tⁿ` are subcomplexes of `Tⁿ ⊗ D`. -/
theorem isSub_fst {A : C.X → Prop} (hA : C.IsSub A) : (C.tensor D).IsSub fun p ↦ A p.1 := by
  rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h hτ
  rcases tensor_d_ne_zero h with ⟨h₁, -⟩ | ⟨rfl, -⟩
  · exact hA _ _ h₁ hτ
  · exact hτ

/-- **Ladder hypothesis for `W`**: for a cover `A ∪ B` of `Tⁿ` by subcomplexes, `φ_W` sends
cochains vanishing on `B ⊗ CP` to chains of `A ⊗ CP` (and symmetrically). -/
theorem torusCP.local (hm : 2 ≤ m) {A B : (torus m n).X → Prop} (hA : (torus m n).IsSub A)
    (hB : (torus m n).IsSub B) (hcov : ∀ σ, A σ ∨ B σ) (σ τ : (torusCP m n).X)
    (h : (torusCP.duality m n).hom.f σ τ ≠ 0) (hτ : ¬B τ.1) : A σ.1 := by
  rw [torusCP.duality, SymDuality.tensor_hom_f, mul_apply, Finset.sum_eq_single τ
    (fun κ _ hκ ↦ by simp [koszul, diagonal_apply_ne _ hκ]) (by simp), kronecker_apply] at h
  exact (torus.isCellLocal_duality m n hm).local hA hB hcov _ _
    (left_ne_zero_of_mul (left_ne_zero_of_mul h)) hτ

variable {V : Type*} [CategoryTheory.Category V] [CategoryTheory.Preadditive V]
  {J : HSFormal.Compression.StrictInvolution V}

/-- `W` as an M1 strictly symmetric Poincaré complex of dimension `n + 4`. -/
def torusCP.symPoincare (R : MatRealization J) : HSFormal.LTheory.SymPoincare J (n + 4) :=
  R.symPoincare (torusCP.duality m n)

end TorusCP

end BasedComplex

end HSFormal.Cubical
