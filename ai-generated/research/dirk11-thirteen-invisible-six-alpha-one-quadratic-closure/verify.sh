#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
r="$(cd -- "${1:-..}" && pwd)"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
d="$(mktemp -d)"
trap 'rm -rf -- "$d"' EXIT
python3 coordinate-audit.py
python3 project.py --research "$r" --out "$d"
for c in ratio c2 old full; do
    python3 rank.py --research "$r" --factor "$d/$c.txt"
done
for c in m1 mY2 contact Fn-loss F1 F2 H3 H5; do
    python3 alternate.py "$c" --research "$r"
done
