#!/usr/bin/env bash
set -euo pipefail
r="$(cd -- "${1:-$(dirname -- "$0")/..}" && pwd)"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
(cd "$r/dirk11-thirteen-invisible-six-alpha-one-beta-two-zero-fifth"; python3 ordinary.py; python3 coordinate-audit.py)
(cd "$r/dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge"; python3 old-fit.py; python3 clock.py)
(cd "$r/dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one"; python3 clock.py; python3 rank.py)
(cd "$r/dirk11-thirteen-invisible-six-alpha-one-zero-fifth-transfer"; bash verify.sh --research "$r")
(cd "$r/dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth"; python3 coordinate-audit.py; bash verify.sh)
