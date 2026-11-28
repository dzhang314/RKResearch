#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
r="${1:-..}"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
python3 replay.py F1 --research "$r"
python3 replay.py F2 --research "$r"
