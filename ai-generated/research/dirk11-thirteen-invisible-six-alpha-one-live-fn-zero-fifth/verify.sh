#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
d="$(mktemp -d)"
trap 'rm -rf -- "$d"' EXIT
python3 project.py --output "$d"
for case in ratio c2 old full; do
  python3 rank.py "$case" "$d/$case.txt"
done
