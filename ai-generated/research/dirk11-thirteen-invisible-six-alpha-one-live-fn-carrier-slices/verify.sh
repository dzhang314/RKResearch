#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
data="$(mktemp -d)"
trap 'rm -rf "$data"' EXIT
export PYTHONDONTWRITEBYTECODE=1
for chart in zero-carrier ghost-fifth; do
  python3 proof.py --chart "$chart" --out "$data"
  for f in "$data/$chart"*.txt; do
     python3 proof.py --chart "$chart" --factor "$f" --p 103
  done
done
