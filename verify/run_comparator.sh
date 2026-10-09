#!/usr/bin/env bash
# Runs leanprover/comparator on Challenge.lean / Solution.lean with comparator.json
# (theorem hilbert_smith; axioms propext, Quot.sound, Classical.choice; Lean kernel + nanoda).
# `verify/run_comparator.sh comparator_fc.json` runs it on FCChallenge.lean / FCSolution.lean
# (the Formal Conjectures variants) instead.
# Prerequisites: `lake exe cache get` in the project root, then verify/build_tools.sh.
# Comparator builds Challenge and Solution itself, in its landrun sandbox; any earlier build
# outputs of these two modules are deleted first. HSFormal and TauCeti are built inside the
# sandbox too, unless they were already built.
# COMPARATOR_SYSTEMD=1 runs it the way the comparator README prescribes, under
# `systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty` (needs a systemd user
# session; guards against a landrun vulnerability fixed in Linux 7.1).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
TOOLS=$(cd "${TOOLS_DIR:-$HERE/_tools}" 2> /dev/null && pwd) || {
  echo "error: no tools directory; run verify/build_tools.sh" >&2; exit 1; }
export PATH="$TOOLS/bin:$HOME/.elan/bin:$PATH"
for t in comparator landrun lean4export nanoda_bin; do
  command -v "$t" > /dev/null || { echo "error: $t not found; run verify/build_tools.sh" >&2; exit 1; }
done
cd "$ROOT"
CONFIG=${1:-comparator.json}
read -r CHALLENGE SOLUTION < <(python3 -c 'import json,sys; c=json.load(open(sys.argv[1]));
print(c["challenge_module"], c["solution_module"])' "$CONFIG")
# Landlock probe, with the landrun options comparator uses for its builds (`--best-effort`, read-only
# `/`, writable `.lake`): a write outside `.lake` must be denied. On kernels without Landlock ABI v2
# (Linux < 5.19), without Landlock enabled, or where seccomp blocks it, `--best-effort` silently
# applies no restriction at all, and comparator's sandbox would be void.
mkdir -p .lake
probe=$ROOT/.landlock-probe
rm -f "$probe" .lake/.landlock-probe
landrun --best-effort --ro / --rw /dev -ldd -add-exec --rwx "$ROOT/.lake" -- touch .lake/.landlock-probe \
  > /dev/null 2>&1 || true
landrun --best-effort --ro / --rw /dev -ldd -add-exec --rwx "$ROOT/.lake" -- touch "$probe" \
  > /dev/null 2>&1 || true
if [[ ! -e .lake/.landlock-probe ]]; then
  echo "error: landrun does not run here (it could not write inside .lake)" >&2; exit 1
fi
rm -f .lake/.landlock-probe
if [[ -e $probe ]]; then
  rm -f "$probe"
  echo "error: Landlock is not enforced (a sandboxed write outside .lake succeeded); comparator's" \
    "sandbox needs Linux >= 5.19 with Landlock enabled" >&2
  exit 1
fi
echo "Landlock probe: writes outside .lake are denied in landrun's sandbox."
rm -f .lake/build/lib/lean/"$CHALLENGE".* .lake/build/lib/lean/"$SOLUTION".* \
      .lake/build/ir/"$CHALLENGE".* .lake/build/ir/"$SOLUTION".*
if [[ ${COMPARATOR_SYSTEMD:-0} == 1 ]]; then
  exec systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
    --working-directory "$(pwd)" -- lake env comparator "$CONFIG"
else
  exec lake env comparator "$CONFIG"
fi
