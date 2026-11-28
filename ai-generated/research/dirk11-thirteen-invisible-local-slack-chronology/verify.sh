#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
r="$(cd "$1" && pwd)"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
python3 repeat.py "$r" --prime 103
python3 four-clean.py "$r" --prime 103
