#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
for x in m1 mY2 contact Fn-loss; do
  python3 proof.py "$x"
done
