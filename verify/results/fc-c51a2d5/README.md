# Comparator record: Formal Conjectures variants at `c51a2d5`

Clean run of `verify/run_comparator.sh comparator_fc.json` and
`verify/run_safeverify.sh FCChallenge FCSolution` on a fresh clone of this repository at
`c51a2d5da2d2264372908b1284bb6b655948a38f`, on 2026-10-10, as an unprivileged user
(`uid=30033(verifier)`), Linux 6.18 with Landlock enforced (the script's probe passed).

Steps (as that user, from an empty home directory):

```sh
git clone https://github.com/adbrw/HS_proof hs && cd hs && git checkout c51a2d5
lake exe cache get                                # Mathlib oleans only
verify/build_tools.sh                             # tools from pinned commits
verify/run_comparator.sh comparator_fc.json       # comparator_fc.log
verify/run_safeverify.sh FCChallenge FCSolution   # safeverify_fc.log, safeverify_report_FCSolution.json
```

Nothing was compiled before comparator except the Mathlib cache: comparator built `FCChallenge`,
then `FCSolution` with the `HSFormal` and `TauCeti` modules, inside its landrun sandbox
(comparator's assumptions 2 and 6 hold). Comparator was run without the `systemd-run` wrapper
(`COMPARATOR_SYSTEMD=1`), since the container has no systemd user session.

| File | |
|---|---|
| `RECORD.txt` | tool revisions, permitted-axiom policy (`comparator_fc.json`), SHA-256 of the inputs and of the two exports, SHA-256 of the logs |
| `comparator_fc.log` | full comparator output; last line `Your solution is okay!` (nanoda and the Lean kernel accept) |
| `safeverify_fc.log`, `safeverify_report_FCSolution.json` | SafeVerify output; `SafeVerify check passed.` |
| `build_tools.log` | build of comparator, lean4export, landrun and SafeVerify |

Comparator keeps its exports in memory. The export digests in `RECORD.txt` are of
`lean4export <module> -- <decls>` run afterwards with the same `lean4export` binary on the same
build, for the declaration list comparator printed (`Exporting #[...]`); each export was generated
twice and was byte-identical both times. The challenge export depends only on `FCChallenge.lean`
and Mathlib `1a547d8`, so its digest can be reproduced without building the proof.
