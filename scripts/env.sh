# Source this file (`. scripts/env.sh`) before running lake in this project.
# It makes Lake fetch TauCeti's modules from TauCeti's public olean cache instead of compiling them.
_here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
export LAKE_CONFIG="$_here/lake-cache.toml"
export LAKE_ARTIFACT_CACHE=true
unset _here
