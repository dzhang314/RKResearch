#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
python3 old-repeated.py
python3 proof.py H3
python3 proof.py H5
