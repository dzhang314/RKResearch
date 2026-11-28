#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 audit-x.py
python3 verify-product.py --check-bits --out "$out"
python3 certify-caps.py --factors "$out"
python3 certify-caps.py --factors "$out" --factor "$out/02.txt"
for f in "$out"/*.txt; do
  python3 joint.py "$f"
done
