# Hilbert–Smith conjecture: Lean 4 formalization

`Challenge.lean` states the Hilbert–Smith conjecture as the theorem `hilbert_smith` (imports only
Mathlib, proof `sorry`). `Solution.lean` proves the same statement as `HSFormal.hilbertSmith n M G`.
`HSFormal/` (238 modules) is the proof: exactly the import closure of
`HSFormal/HilbertSmithNegK.lean`, where `HSFormal.hilbertSmith` is proved; `HSFormal.lean` is the
library root importing it. Axioms used: `propext`, `Classical.choice`, `Quot.sound`.

## Contents

| Path | |
|---|---|
| `Challenge.lean` | statement, `import Mathlib` only |
| `Solution.lean` | same statement, proof `HSFormal.hilbertSmith n M G` |
| `HSFormal.lean`, `HSFormal/` | the proof (library `HSFormal`); `HSFormal/Brouwer/LICENSE` is the MIT licence of the five `HSFormal/Brouwer/` files |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lean `v4.35.0-rc3`; mathlib `1a547d8a48a8fa7877d2decb69d7294723bb0187`; TauCeti `c7af81f021f76fa11afcd61c894e5fc861ab6e78` |
| `comparator.json` | comparator configuration |
| `verify/build_tools.sh` | builds comparator, lean4export, landrun and SafeVerify at pinned commits |
| `verify/safeverify-v435.patch` | ports SafeVerify (Lean v4.27) to Lean v4.35.0-rc3 |
| `verify/run_comparator.sh`, `verify/run_safeverify.sh` | run the two checkers |

## Requirements

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

## Running

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

## What the checkers establish

**comparator** ([leanprover/comparator](https://github.com/leanprover/comparator) `fd5d5bcf14177b187f66d4502071268d877887c3`,
unmodified; lean4export `66f1fb4bc256072069767fce52d39480e4524869`; landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`;
`nanoda_bin` from the Lean toolchain). It builds both modules in the sandbox and exports them with
lean4export, then checks that
1. `hilbert_smith` in `Solution` has the same statement as in `Challenge`, and every constant the
   statement uses (`LieGroup`, `ChartedSpace`, `EuclideanSpace`, …, down to `Init`) has the same
   definition in both;
2. the proof uses only the axioms in `comparator.json`;
3. the exported solution, which contains `hilbert_smith` and every declaration it depends on
   (all of the `HSFormal`, `TauCeti` and Mathlib declarations used by the proof), is accepted by
   the Lean kernel and by the nanoda kernel (`"enable_nanoda": true`).

**SafeVerify** ([GasStationManager/SafeVerify](https://github.com/GasStationManager/SafeVerify)
`b291b588a53999a7e837dda61c7dbfe8c550c814` + `verify/safeverify-v435.patch`). It reads
`Challenge.olean` (target) and `Solution.olean` (submission), replays the declarations of each
file through the kernel (`Environment.replay`, then a second kernel check of each theorem's
proof term), rejects `unsafe` constants in either file, and checks that `hilbert_smith` occurs in
the submission with the same type, is a theorem, and depends only on `propext`, `Quot.sound`,
`Classical.choice`. The submission must import every module the target imports (transitively),
which is why `Solution.lean` also has `import Mathlib`. (`--disallow-partial` rejects constants of
the two files with `partial` safety other than compiler-generated `*._unsafe_rec`; a source-level
`partial def` compiles to an `opaque`, which this flag does not reject.) As in
upstream SafeVerify, only the declarations of the two files are replayed, not those of their
imports; the axiom check does traverse imported declarations. The kernel check of the imported
proof is comparator's step 3. `verify/run_safeverify.sh` recompiles `Challenge.olean` from
`Challenge.lean`; the Mathlib `.olean` files both sides import are taken as they are in `.lake`
(from `lake exe cache get`, and writable by comparator's sandboxed `Solution` build), so for a
SafeVerify verdict independent of comparator's sandbox, run it in a separate unpacked copy.

The port (`verify/safeverify-v435.patch`, against `b291b58`) changes no check:
- `lean-toolchain` → `leanprover/lean4:v4.35.0-rc3`; the mathlib-pinned `lakefile.lean` and
  `lake-manifest.json` are replaced by a `lakefile.toml` requiring only `lean4-cli` (written by
  `verify/build_tools.sh`, pinned to the `Cli` revision of this project's manifest).
- `SafeVerify/CollectAxioms.lean`: Lean v4.27's `Lean.CollectAxioms.collect`, which is private in
  v4.35 (where `Lean.collectAxioms` reads per-module axiom tables stored in the `.olean` files).
  SafeVerify keeps traversing every reachable constant itself.
- The import-superset check reads the transitive module sets from the environments already
  imported for the two replays, instead of importing both files' imports a second time (memory);
  it now runs after the two replays instead of before.
