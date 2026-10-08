# Integral tail signatures and the Hilbert–Smith conjecture

**[`HSproof.pdf`](HSproof.pdf)**: *Integral tail signatures and the Hilbert–Smith conjecture*,
A. Dabrowski's AI agents, October 8, 2026, 17 pp.

> **Theorem 1.1** (p-adic exclusion). For every prime p, a continuous action of ℤ_p on a connected
> finite-dimensional manifold has nontrivial kernel.
>
> **Corollary 1.2** (Hilbert–Smith). A second-countable locally compact Hausdorff group acting
> continuously and effectively on such a manifold is a Lie group with its given topology.

Manifolds are Hausdorff and second countable, and may have boundary. All actions are jointly
continuous. Corollary 1.2 follows from Theorem 1.1 by the standard reduction to p-adic exclusion,
using locally compact group structure and Newman's theorem [Pa19].

The obstruction is an integer signature tail. The proof has two parts:

- **Divisibility** (§§2–6, Theorem 4.3). Take cyclic groups G_i = C_{p^{a_i}} with index-p
  subgroups P_i, and a fixed compact free C_p-space T. Tensoring with the positive permutation
  form τ_i = ℚ[G_i/P_i] is locally p copies of the identity. Controlled Mayer–Vietoris over a
  finite cover makes p − τ ⊗ (−) nilpotent. Equivariant signature characters then show that
  every class in L_4(A_G(T)) has ordinary signatures eventually divisible by p.
- **Realization** (§§7–13, Proposition 13.1). An effective ℤ_p-action gives a class with
  signature tail 1. Coordinate averaging gives an invariant degree-one sphere control map. Fine
  local chain models turn finite quotient representatives into a homotopy action. Free sheets
  cancel the detector displacement, and averaging gives a duality-compatible homotopy idempotent.
  Its normalized Poincaré corner forgets to the scalar manifold germ of Sⁿ × CP². Successive
  localization boundaries recover one copy of CP², up to sign.

The two parts together give 1 ∈ pℤ, a contradiction. The paper uses the following controlled
machinery from the literature: Karoubi localization [CP95], controlled Poincaré–Lefschetz duality
[Ran99], algebraic Poincaré pairs and unions [Ran80I, Ran80II], and idempotent splitting [BS01].
It works out the local carrier and normalization calculations this setting needs.

## Lean 4 formalization

The rest of the repository is a Lean 4 / Mathlib formalization of Corollary 1.2, together with
the scripts that check it.

`Challenge.lean` states the Hilbert–Smith conjecture as the theorem `hilbert_smith` (imports only
Mathlib, proof `sorry`). `Solution.lean` proves the same statement as `HSFormal.hilbertSmith n M G`.
`HSFormal/` (238 modules) is the proof: exactly the import closure of
`HSFormal/HilbertSmithNegK.lean`, where `HSFormal.hilbertSmith` is proved; `HSFormal.lean` is the
library root importing it. Axioms used: `propext`, `Classical.choice`, `Quot.sound`.

### Contents

| Path | |
|---|---|
| `HSproof.pdf` | the paper |
| `Challenge.lean` | statement, `import Mathlib` only |
| `Solution.lean` | same statement, proof `HSFormal.hilbertSmith n M G` |
| `HSFormal.lean`, `HSFormal/` | the proof (library `HSFormal`); `HSFormal/Brouwer/LICENSE` is the MIT licence of the five `HSFormal/Brouwer/` files |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lean `v4.35.0-rc3`; mathlib `1a547d8a48a8fa7877d2decb69d7294723bb0187`; TauCeti `c7af81f021f76fa11afcd61c894e5fc861ab6e78` |
| `comparator.json` | comparator configuration |
| `verify/build_tools.sh` | builds comparator, lean4export, landrun and SafeVerify at pinned commits |
| `verify/safeverify-v435.patch` | ports SafeVerify (Lean v4.27) to Lean v4.35.0-rc3 |
| `verify/run_comparator.sh`, `verify/run_safeverify.sh` | run the two checkers |

### Requirements

- Linux ≥ 5.19 with Landlock enabled (in a container, seccomp must allow the `landlock_*`
  syscalls), for landrun, comparator's sandbox. Comparator calls landrun with `--best-effort`:
  without Landlock ABI v2 (Linux < 5.19) the whole ruleset is silently dropped, and network
  restriction (≥ 6.7) and IPC scoping (Landlock ABI v6, ≥ 6.12) are dropped on older kernels.
  `verify/run_comparator.sh` first checks that a sandboxed write outside `.lake` is denied, and
  stops otherwise.
- [elan](https://github.com/leanprover/elan), git, curl (used by `lake exe cache get`), `which`
  (used by comparator), Go ≥ 1.24 (to build landrun).
- About 15 GB of free disk and 16 GB of RAM.
- Run as an unprivileged user (comparator's assumption 6).

### Running

From this directory:

```sh
lake exe cache get              # Mathlib and its dependencies, prebuilt
verify/build_tools.sh           # tools, into verify/_tools/
verify/run_comparator.sh        # expected last line: Your solution is okay!
verify/run_safeverify.sh        # expected last line: SafeVerify check passed.
```

Run comparator before anything compiles `Solution.lean` or `HSFormal` (comparator's assumption 2):
`verify/run_comparator.sh` deletes earlier build outputs of `Challenge` and `Solution`, and
comparator then compiles `Challenge`, then `Solution` with the `HSFormal` modules and the
`TauCeti` modules they import (those not already built), inside its landrun sandbox.
`COMPARATOR_SYSTEMD=1 verify/run_comparator.sh` runs comparator under
`systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty`, as its README prescribes
(needs a systemd user session).

To only compile the proof: `lake build` (builds `HSFormal`), then
`lake env lean --stdin <<< 'import HSFormal.HilbertSmithNegK
#print axioms HSFormal.hilbertSmith'`.
