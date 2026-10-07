import HSFormal.Inputs.Lemma7Characters
import HSFormal.Inputs.Lemma7Padic

/-!
# [Tao11, Lemma 7]: a compact torsion-free group contains `ℤ_p`

`HSFormal.Lemma7.compactTorsionFreeContainsPadic` proves, with exactly the statement body of
`HSFormal.CompactTorsionFreeContainsPadic` (`HSFormal/WeakInputs.lean`), that a nontrivial
torsion-free compact Hausdorff second-countable group contains a continuously embedded `ℤ_[p]`.

Pick `g ≠ 1` and pass to the compact monothetic group `B = cl ⟨g⟩`. Its continuous circle
characters separate points (`HSFormal.Lemma7.exists_char_ne_one`, from Peter–Weyl in TauCeti),
so `HSFormal.Lemma7.exists_padic_embedding_of_chars` (the one-character-at-a-time tower argument)
embeds some `ℤ_[p]` in `B`, hence in the ambient group.
-/

namespace HSFormal.Lemma7

/-- **[Tao11, Lemma 7].** Statement body identical to `HSFormal.CompactTorsionFreeContainsPadic`. -/
theorem compactTorsionFreeContainsPadic :
    ∀ (C : Type) [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
      [T2Space C] [SecondCountableTopology C], Nontrivial C →
      (∀ g : C, IsOfFinOrder g → g = 1) →
      ∃ (p : ℕ) (_ : Fact p.Prime) (ι : Multiplicative ℤ_[p] →* C),
        Continuous ι ∧ Function.Injective ι := by
  intro C _ _ _ _ _ _ _ htf
  obtain ⟨g, hg⟩ := exists_ne (1 : C)
  set Bs : Subgroup C := (Subgroup.zpowers g).topologicalClosure
  have hcomm : ∀ a b : Bs, a * b = b * a :=
    fun a b => (Subgroup.isMulCommutative_topologicalClosure (Subgroup.zpowers g)).is_comm.comm a b
  let _ : CommGroup Bs := { (inferInstance : Group Bs) with mul_comm := hcomm }
  have _ : CompactSpace Bs :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  let g' : Bs := ⟨g, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers g)⟩
  have himg : ((↑) : Bs → C) '' (Subgroup.zpowers g' : Set Bs) = Subgroup.zpowers g := by
    have := Subgroup.coe_map Bs.subtype (Subgroup.zpowers g')
    rw [MonoidHom.map_zpowers] at this
    exact this.symm
  have hdense : Dense (Subgroup.zpowers g' : Set Bs) := by
    intro b
    rw [closure_subtype, himg, ← Subgroup.topologicalClosure_coe]
    exact b.2
  have hsep : ∀ b : Bs, b ≠ 1 → ∃ χ : Bs →* Circle, Continuous χ ∧ χ b ≠ 1 :=
    fun b hb => exists_char_ne_one g' hdense b hb
  have _ : SecondCountableTopology Bs :=
    TopologicalSpace.Subtype.secondCountableTopology (Bs : Set C)
  have _ : Nontrivial Bs := ⟨⟨g', 1, fun h => hg (congrArg Subtype.val h)⟩⟩
  have htfB : ∀ b : Bs, IsOfFinOrder b → b = 1 := by
    intro b hb
    apply Subtype.ext
    exact htf _ ((Function.Injective.isOfFinOrder_iff (f := Bs.subtype)
      Bs.subtype_injective).2 hb)
  obtain ⟨p, hp, ι, hc, hinj⟩ := exists_padic_embedding_of_chars htfB hsep
  exact ⟨p, hp, Bs.subtype.comp ι, continuous_subtype_val.comp hc,
    Subtype.val_injective.comp hinj⟩

end HSFormal.Lemma7

