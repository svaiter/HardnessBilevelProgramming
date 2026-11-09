#!/usr/bin/env bash
# One-time setup: Mathlib oleans, then the input-to-output mappings of TauCeti's olean cache.
# TauCeti artifacts are downloaded lazily, only for the modules the Semialgebraic companion imports.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/env.sh
lake exe cache get
lake cache get --package=TauCeti --service tauceti-public --repo TauCetiProject/TauCeti --mappings-only
