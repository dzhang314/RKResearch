#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
r="${1:-..}"
engine="${2:-$r/dirk11-thirteen-invisible-six-alpha-one-beta-one-alternate-f1-f2}"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
python3 "$engine/replay.py" H3 --research "$r"
python3 "$engine/replay.py" H5 --research "$r"
