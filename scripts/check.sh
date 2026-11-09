#!/usr/bin/env bash
# Full build + hygiene + axiom checks for HardnessBilevel (core library) and HardnessBilevelUnconditional
# (proved instances of the assumption classes and assumption-free corollaries).
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/env.sh
echo "== build =="
lake build 2>&1 | grep -v "module system" | tail -2
echo "== hygiene: sorry / admit / native_decide / axiom / unsafe / implemented_by / extern / opaque =="
# (mentions inside backticks or on comment lines are allowed; the axiom checks below are the real guard)
SRC="HardnessBilevel HardnessBilevel.lean HardnessBilevelUnconditional HardnessBilevelUnconditional.lean"
PAT='\b(sorry|admit|native_decide|implemented_by|extern)\b|^\s*(private\s+|protected\s+)?(axiom|unsafe|opaque)\b'
SKIP='`[^`]*(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern|opaque)|^[^:]+:[0-9]+:\s*(--|/-|\*)'
if grep -rnE "$PAT" $SRC | grep -vE "$SKIP" | grep -q .; then
  grep -rnE "$PAT" $SRC | grep -vE "$SKIP"
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
if grep -rnE 'attribute\s*\[[^]]*instance' HardnessBilevel HardnessBilevelUnconditional; then echo "FAIL: instance attribute set outside an instance declaration"; exit 1; fi
echo "ok (each is proved; its axioms are printed below)"
echo "== instance search fails in the core library =="
if [ -n "$(lake lean scripts/CheckNoInstance.lean 2>/dev/null)" ]; then
  lake lean scripts/CheckNoInstance.lean 2>/dev/null; echo "FAIL: an instance of an assumption class is in scope in the core library"; exit 1
fi
echo "ok"

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
# every theorem of HardnessBilevelUnconditional/Main.lean must be listed in the axiom check
for t in $(grep -oE '^theorem [A-Za-z0-9_]+' HardnessBilevelUnconditional/Main.lean | awk '{print $2}'); do
  grep -q "^#print axioms Unconditional.$t\$" scripts/CheckAxiomsUnconditional.lean || { echo "FAIL: $t is not axiom-checked"; exit 1; }
done
echo "OK: all listed theorems depend only on propext, Classical.choice, Quot.sound"
