#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
export PYTHONDONTWRITEBYTECODE=1
sha=293539c6eccba4414855ac08c2223913357373f0832440a98885c7f0c7af089e
python3 extend-check.py "$sha" --out "$tmp"
for f in "$tmp"/old-linear*.txt; do
  python3 extend-check.py "$sha" --factor "$f" --p 103
done
