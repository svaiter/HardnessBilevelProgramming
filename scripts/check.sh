#!/usr/bin/env bash
# Full build + hygiene + axiom check for the HardnessBilevel library.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== build =="
lake build 2>&1 | grep -v "module system" | tail -2
echo "== hygiene: sorry / axiom / native_decide / admit =="
# (mentions inside backticks or on comment lines are allowed; the axiom check below is the real guard)
if grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' HardnessBilevel HardnessBilevel.lean | grep -vE '`(sorry|admit|native_decide|axiom)|^[^:]+:[0-9]+:\s*(--|/-|\*)' | grep -q .; then
  grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' HardnessBilevel HardnessBilevel.lean | grep -vE '`(sorry|admit|native_decide|axiom)|^[^:]+:[0-9]+:\s*(--|/-|\*)'
  echo "FAIL: forbidden token"; exit 1
fi
echo "none"
echo "== hygiene: no instance of the assumption classes =="
if grep -rnE '^\s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(scoped\s+|local\s+)?instance\b.*(HasSemialgebraicProjections|HasFinitenessTheorem|HasGrowthBound)' HardnessBilevel; then echo "FAIL: instance of an assumption class"; exit 1; fi
if grep -rnE '^\s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(scoped\s+|local\s+)?instance\b' HardnessBilevel/Assumptions; then echo "FAIL: instance declared in Assumptions/"; exit 1; fi
echo "none"
echo "== axioms of the main theorems =="
lake env lean scripts/CheckAxioms.lean | tee /tmp/axioms.txt
if grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]|^$" /tmp/axioms.txt | grep -q .; then echo "FAIL: unexpected axiom or error"; exit 1; fi
echo "OK: all listed theorems depend only on propext, Classical.choice, Quot.sound"
