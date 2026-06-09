#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_BIN="/home/user/LEAN/lean4/build/release/stage1/bin"
export PATH="$LEAN_BIN:$PATH"
cd "$SCRIPT_DIR"
echo "=== csv Test Suite ==="
lake build 2>&1
echo ""
lake exe test 2>&1
echo ""
echo "=== Done ==="
