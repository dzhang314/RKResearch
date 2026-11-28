#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 coordinate-audit.py
python3 project.py --output "$d"
for n in ratio c2 old full; do
  python3 rank.py "$n" "$d/$n.txt"
done
