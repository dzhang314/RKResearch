#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
research=$(cd -- "${1:-"$here/.."}" && pwd)
export PYTHONDONTWRITEBYTECODE=1
export SYMPY_GROUND_TYPES="${SYMPY_GROUND_TYPES:-flint}"
python3 "$here/verify.py"
(cd "$research"; sha256sum --status -c "$here/arithmetic-dependencies.sha256")

# These are arithmetic dependency checks, not a proof of the tableau ingress.
python3 "$research/dirk11-thirteen-invisible-local-late-early-completion/project.py" --research "$research" --prime 101 --prime 103
python3 "$research/dirk11-thirteen-invisible-local-fourth-return/minus.py"
python3 "$research/dirk11-thirteen-invisible-local-fourth-return/nonminus.py" --research "$research" --prime 101
python3 "$research/dirk11-thirteen-invisible-local-live-fourth-old-event/project.py" --prime 101 --prime 107
python3 "$research/dirk11-thirteen-invisible-local-late-matched-fifth/project.py" --prime 101 --prime 107
python3 "$research/dirk11-thirteen-invisible-local-mismatched-fifth-zero-head/identities.py"
python3 "$research/dirk11-thirteen-invisible-local-four-pair-closure/project.py" --prime 103 --prime 107
