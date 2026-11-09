#!/usr/bin/env bash
# Full build + hygiene + axiom checks for HardnessBilevel (core library) and HardnessBilevelUnconditional
# (proved instances of the assumption classes and assumption-free corollaries).
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/env.sh
echo "== build =="
lake build 2>&1 | grep -v "module system" | tail -2
echo "== hygiene: sorry / axiom / native_decide / admit =="
# (mentions inside backticks or on comment lines are allowed; the axiom checks below are the real guard)
SRC="HardnessBilevel HardnessBilevel.lean HardnessBilevelUnconditional HardnessBilevelUnconditional.lean"
if grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' $SRC | grep -vE '`(sorry|admit|native_decide|axiom)|^[^:]+:[0-9]+:\s*(--|/-|\*)' | grep -q .; then
  grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' $SRC | grep -vE '`(sorry|admit|native_decide|axiom)|^[^:]+:[0-9]+:\s*(--|/-|\*)'
  echo "FAIL: forbidden token"; exit 1
fi
echo "none"
echo "== hygiene: no instance of the assumption classes in the core library =="
if grep -rnE '^\s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(scoped\s+|local\s+)?instance\b.*(HasSemialgebraicProjections|HasFinitenessTheorem|HasGrowthBound)' HardnessBilevel; then echo "FAIL: instance of an assumption class in the core library"; exit 1; fi
if grep -rnE '^\s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(scoped\s+|local\s+)?instance\b' HardnessBilevel/Assumptions; then echo "FAIL: instance declared in Assumptions/"; exit 1; fi
echo "none"
echo "== hygiene: the instances of the assumption classes are exactly the three proved ones =="
found="$(grep -rhoE '^\s*instance\s+\S+\s*:\s*(HasSemialgebraicProjections|HasFinitenessTheorem|HasGrowthBound)\b' HardnessBilevelUnconditional | sed -E 's/^\s*//' | sort)"
expected="$(printf '%s\n' 'instance instHasFinitenessTheorem : HasFinitenessTheorem' 'instance instHasGrowthBound : HasGrowthBound' 'instance instHasSemialgebraicProjections : HasSemialgebraicProjections' | sort)"
if [ "$found" != "$expected" ] || [ "$(grep -rcE '^\s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(scoped\s+|local\s+)?instance\b' HardnessBilevelUnconditional | awk -F: '{s+=$2} END {print s}')" != 3 ]; then
  echo "$found"; echo "FAIL: unexpected instance declarations in HardnessBilevelUnconditional"; exit 1
fi
echo "ok (each is proved; its axioms are printed below)"

# check_axioms FILE: every `#print axioms` of FILE must report exactly the three standard axioms.
check_axioms() {
  local file="$1" out n
  out="$(mktemp)"
  lake lean "$file" 2>/dev/null | tee "$out"
  n="$(grep -c '^#print axioms' "$file")"
  if grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]|^$" "$out" | grep -q .; then
    echo "FAIL: unexpected axiom or error in $file"; exit 1
  fi
  if [ "$(grep -c 'depends on axioms' "$out")" != "$n" ]; then
    echo "FAIL: expected $n axiom reports from $file"; exit 1
  fi
}
echo "== axioms of the main theorems (core library; assumptions are class binders) =="
check_axioms scripts/CheckAxioms.lean
echo "== axioms of the proved instances and of the assumption-free corollaries =="
check_axioms scripts/CheckAxiomsUnconditional.lean
echo "OK: all listed theorems depend only on propext, Classical.choice, Quot.sound"
