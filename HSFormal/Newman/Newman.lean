module

public import HSFormal.Newman.Transfer
public import HSFormal.Newman.Main

@[expose] public section

/-!
# Newman's theorem for prime-order periodic homeomorphisms

`HSFormal.NewmanPrimeOrder` (the published input of `HSFormal.WeakInputs`), proved: the mod-`p`
transfer `degreeEqZeroOfFree` (N7) combined with Claims 1, 2′ and the main argument (N8, N9).
See `blueprint/newman.md`.
-/

namespace HSFormal.Newman

theorem newmanPrimeOrder : NewmanPrimeOrder :=
  newmanPrimeOrder_of_degreeEqZeroOfFree degreeEqZeroOfFree

end HSFormal.Newman
