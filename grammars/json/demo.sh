#!/usr/bin/env bash
set -euo pipefail

# JSON Query Engine Demo
# Demonstrates all five query types against grammars-v4's example1.json

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_BIN="/home/user/LEAN/lean4/build/release/stage1/bin"
export PATH="$LEAN_BIN:$PATH"

echo "=== JSON Query Engine Demo ==="
echo ""

# 1. FIELD PATH EXTRACTION
echo "--- 1. Field Path Extraction ---"
echo "Path: glossary.GlossDiv.title"
echo "Path: glossary.GlossDiv.GlossList.GlossEntry.ID"
echo "Path: glossary.GlossDiv.GlossList.GlossEntry.GlossDef.para"
echo "Path: glossary.GlossDiv.GlossList.GlossEntry.GlossDef.GlossSeeAlso"

# 2. PATH WILDCARDS
echo ""
echo "--- 2. Path Wildcards ---"
echo "Path: glossary.*.title        (wildcard one level)"
echo "Path: **.ID                    (deep wildcard)"
echo "Path: **.GlossSeeAlso          (deep wildcard)"

# 3. VALUE PATTERN MATCHING
echo ""
echo "--- 3. Value Pattern Matching ---"
echo "Strings starting with 'S':"
echo "Strings containing 'Markup':"
echo "Exact match 'SGML':"

# 4. RECURSIVE FIELD SEARCH
echo ""
echo "--- 4. Recursive Field Search ---"
echo "All 'title' fields at any depth:"
echo "All 'GlossSeeAlso' fields:"

# 5. STRUCTURAL VALIDATION
echo ""
echo "--- 5. Structural Validation ---"
echo "Schema: {glossary: any}"
echo "Schema: {glossary: {GlossDiv: {title: string}}}"

# 6. COMPOSED SELECTORS
echo ""
echo "--- 6. Composed Selectors ---"
echo "glossary.GlossDiv.* (all fields under GlossDiv):"

echo ""
echo "Running query engine..."
echo ""

cd "$SCRIPT_DIR"
lake exe queryDemo

echo ""
echo "=== Done ==="
