# Third-party notices

The repository's original material is offered under Apache-2.0; the root
`LICENSE` contains its terms. Existing third-party material retains its own
copyright, licence and attribution. Citing a mathematical work does not change
the licence of that work.

## Brouwer fixed-point formalization

The five Lean files under `HSFormal/Brouwer/` are adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940d)
at commit `770940d`. Copyright (c) 2026 harfe. They retain the MIT licence,
whose complete permission and disclaimer notice is in
[`HSFormal/Brouwer/LICENSE`](HSFormal/Brouwer/LICENSE), and their existing
file headers describe the port. The root Apache licence does not remove that
MIT notice or replace the upstream terms.

## Lean axiom-collection code

`verify/safeverify-v435.patch` includes a modified port of
[`Lean/Util/CollectAxioms.lean` from Lean v4.27.0](https://github.com/leanprover/lean4/blob/v4.27.0/src/Lean/Util/CollectAxioms.lean),
used to keep a fresh axiom traversal in SafeVerify on Lean v4.35.

Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 licence as described in the file `LICENSE`.
Authors: Leonardo de Moura.

The patch identifies the port and changes the namespace and environment lookup;
the complete Apache-2.0 terms are provided in the repository root `LICENSE`.
The patch's other modifications apply to
[SafeVerify](https://github.com/GasStationManager/SafeVerify/tree/b291b588a53999a7e837dda61c7dbfe8c550c814),
which is distributed under Apache-2.0.

## Formal Conjectures statements

`FCChallenge.lean` and `FCSolution.lean` adapt the Hilbert–Smith statement
variants proposed for `FormalConjectures/HilbertProblems/5.lean` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(issue 6914). The source project is distributed under Apache-2.0 and its
Hilbert's Fifth Problem module carries:

Copyright 2026 The Formal Conjectures Authors.

The local module documentation describes the second-countability hypotheses
and smoothness conclusion used here. The copied statements' precise proposal
revision was not recorded in the original repository.

## External dependencies and checking tools

Pinned dependencies are fetched separately; their source licences remain in
their checkouts. Mathlib, Tau Ceti, plausible, LeanSearchClient, import-graph,
ProofWidgets4, aesop, and Qq use Apache-2.0. Batteries also uses Apache-2.0.
`lean4-cli` uses MIT. Version pins are in `lake-manifest.json`.

The checking scripts fetch Comparator and lean4export under Apache-2.0,
SafeVerify under Apache-2.0, and landrun under MIT. These external tools are not
included as source in this repository. The root licence does not relicense
them. Anyone redistributing dependencies or tool binaries must preserve their
own applicable licence and attribution notices.
