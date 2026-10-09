#!/usr/bin/env bash
# Runs SafeVerify (v4.35 port, see verify/build_tools.sh) with target Challenge.olean and
# submission Solution.olean: every theorem of the target (hilbert_smith) must occur in the
# submission with the same type, a proof without sorry, and only the axioms propext, Quot.sound,
# Classical.choice. The JSON report is written to safeverify_report.json.
# `verify/run_safeverify.sh FCChallenge FCSolution` checks the Formal Conjectures variants instead
# (report: safeverify_report_FCSolution.json).
# Prerequisites: `lake exe cache get` in the project root, then verify/build_tools.sh.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
TOOLS=$(cd "${TOOLS_DIR:-$HERE/_tools}" 2> /dev/null && pwd) || {
  echo "error: no tools directory; run verify/build_tools.sh" >&2; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"
[[ -x $TOOLS/bin/safe_verify ]] || { echo "error: safe_verify not found; run verify/build_tools.sh" >&2; exit 1; }
cd "$ROOT"
CHALLENGE=${1:-Challenge}
SOLUTION=${2:-Solution}
REPORT=safeverify_report.json
[[ $SOLUTION == Solution ]] || REPORT=safeverify_report_$SOLUTION.json
# The target is recompiled from Challenge.lean (a few seconds), rather than taken from an earlier
# build, e.g. comparator's sandboxed one, during which the Solution build could write to .lake.
rm -f .lake/build/lib/lean/"$CHALLENGE".* .lake/build/ir/"$CHALLENGE".*
lake build "$CHALLENGE" "$SOLUTION"
exec lake env "$TOOLS/bin/safe_verify" --disallow-partial --verbose --save "$REPORT" \
  .lake/build/lib/lean/"$CHALLENGE".olean .lake/build/lib/lean/"$SOLUTION".olean
