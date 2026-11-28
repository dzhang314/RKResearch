#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
python3 first-pin.py "$@"
