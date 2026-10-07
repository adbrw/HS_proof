#!/usr/bin/env bash
# Builds the checking tools, at pinned commits, into verify/_tools/ (override with TOOLS_DIR):
#   comparator   leanprover/comparator  fd5d5bc (toolchain v4.35.0-rc3), with its pinned lean4export
#   landrun      Zouuup/landrun         811cfff (sandbox used by comparator; needs Go >= 1.24)
#   nanoda_bin   shipped with the Lean toolchain v4.35.0-rc3 (second kernel for comparator)
#   safe_verify  GasStationManager/SafeVerify b291b58 (Lean v4.27) + verify/safeverify-v435.patch,
#                which ports it to Lean v4.35.0-rc3 (needed to read this project's .olean files)
# Symlinks to the five executables are put in verify/_tools/bin/.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
TOOLS=$(mkdir -p "${TOOLS_DIR:-$HERE/_tools}" && cd "${TOOLS_DIR:-$HERE/_tools}" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
for t in git lake go; do
  command -v "$t" > /dev/null || { echo "error: $t not found (Go >= 1.24 is needed for landrun)" >&2; exit 1; }
done

COMPARATOR_GIT=https://github.com/leanprover/comparator
COMPARATOR_REV=fd5d5bcf14177b187f66d4502071268d877887c3
LANDRUN_GIT=https://github.com/Zouuup/landrun
LANDRUN_REV=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
SAFEVERIFY_GIT=https://github.com/GasStationManager/SafeVerify
SAFEVERIFY_REV=b291b588a53999a7e837dda61c7dbfe8c550c814
CLI_GIT=https://github.com/leanprover/lean4-cli
CLI_REV=843844fa601dd56767b1eb22b7ada5b64d5e567a   # = the project's lake-manifest.json pin

checkout() {  # checkout URL REV DIR
  if [[ ! -d $3/.git ]]; then git clone --quiet "$1" "$3"; fi
  git -C "$3" checkout --quiet --force "$2"
  git -C "$3" clean --quiet -fdx -e .lake
}

mkdir -p "$TOOLS/bin"

echo "== comparator $COMPARATOR_REV"
checkout "$COMPARATOR_GIT" "$COMPARATOR_REV" "$TOOLS/comparator"
(cd "$TOOLS/comparator" && lake build --no-cache lean4export comparator)
ln -sf "$TOOLS/comparator/.lake/build/bin/comparator" "$TOOLS/bin/comparator"
ln -sf "$TOOLS/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" "$TOOLS/bin/lean4export"

echo "== landrun $LANDRUN_REV"
checkout "$LANDRUN_GIT" "$LANDRUN_REV" "$TOOLS/landrun"
(cd "$TOOLS/landrun" && go build -o landrun ./cmd/landrun)
ln -sf "$TOOLS/landrun/landrun" "$TOOLS/bin/landrun"

echo "== nanoda_bin (Lean toolchain)"
nanoda=$(cd "$ROOT" && lean --print-prefix)/bin/nanoda_bin
[[ -x $nanoda ]] || { echo "error: $nanoda not found" >&2; exit 1; }
ln -sf "$nanoda" "$TOOLS/bin/nanoda_bin"

echo "== SafeVerify $SAFEVERIFY_REV + safeverify-v435.patch"
checkout "$SAFEVERIFY_GIT" "$SAFEVERIFY_REV" "$TOOLS/safeverify"
git -C "$TOOLS/safeverify" apply "$HERE/safeverify-v435.patch"
cat > "$TOOLS/safeverify/lakefile.toml" <<TOML
name = "SafeVerify"
defaultTargets = ["SafeVerify", "safe_verify"]

[leanOptions]
autoImplicit = false

[[require]]
name = "Cli"
git = "$CLI_GIT"
rev = "$CLI_REV"

[[lean_lib]]
name = "SafeVerify"

[[lean_exe]]
name = "safe_verify"
root = "Main"
supportInterpreter = true
TOML
(cd "$TOOLS/safeverify" && lake build)
ln -sf "$TOOLS/safeverify/.lake/build/bin/safe_verify" "$TOOLS/bin/safe_verify"

echo "== done: $(ls "$TOOLS/bin" | tr '\n' ' ')"
