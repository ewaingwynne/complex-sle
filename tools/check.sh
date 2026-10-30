#!/usr/bin/env bash
# Project gate. Run from anywhere; exits non-zero on the first failing check.
#   tools/check.sh          full gate (build + all checkers)
#   tools/check.sh --quick  checkers only, no lake build
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

if [[ "${1:-}" != "--quick" ]]; then
  echo "== lake build"
  lake build 2>&1 | grep -v 'could not canonicalize path' | tail -n 20
  test "${PIPESTATUS[0]}" -eq 0
fi

echo "== module headers"
# The checker only sees git-tracked files by default; pass every Lean file explicitly
# so untracked work is checked too.
mapfile -t lean_files < <(find ComplexSLE tools -name '*.lean' 2>/dev/null)
if ((${#lean_files[@]})); then
  python3 -I tools/check_lean_modules.py --root . --max-lines 1500 --files "${lean_files[@]}"
else
  python3 -I tools/check_lean_modules.py --root .
fi

if [[ -f frozen-anchor-manifest.json ]]; then
  echo "== frozen anchors"
  python3 -I tools/check_frozen_anchors.py --root . --manifest frozen-anchor-manifest.json
  if [[ "${1:-}" != "--quick" ]]; then
    echo "== elaborated ABI hashes"
    python3 -I tools/leanprobe.py verify-abi frozen-anchor-manifest.json
  fi
else
  echo "== frozen anchors: no manifest yet; checking for stray placeholders"
  if grep -rnwE 'sorry|admit' --include='*.lean' ComplexSLE; then
    echo "unauthorized placeholder (no manifest exists)"; exit 1
  fi
fi

echo "== forbidden constructs"
# Heartbeat overrides, kernel bypasses, compiler trust, and custom axioms are banned.
pattern='set_option[[:space:]]+(maxHeartbeats|synthInstance\.maxHeartbeats|maxRecDepth|debug\.)|native_decide|implemented_by|@\[extern|^[[:space:]]*(axiom|unsafe)[[:space:]]|decide[[:space:]]*:=[[:space:]]*true|Lean\.ofReduceBool|trustCompiler'
if grep -rnE "$pattern" --include='*.lean' ComplexSLE; then
  echo "forbidden construct found"; exit 1
fi
echo "ALL CHECKS PASSED"
