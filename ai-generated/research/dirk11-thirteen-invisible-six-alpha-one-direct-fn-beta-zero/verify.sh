#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
a=$(mktemp -d)
trap 'rm -rf "$a"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 audit-beta0.py
for row in Jleader one-reverse two-reverse; do
  python3 proof.py --case "$row" --out "$a/$row"
done
python3 common.py "$a"
python3 proof.py --cap-dir "$a/common"
for f in "$a"/common/*.txt; do
  python3 proof.py --factor "$f" --p 103
done
