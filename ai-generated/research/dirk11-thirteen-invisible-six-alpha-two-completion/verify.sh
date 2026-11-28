#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
repo="$(cd -- "$1" && pwd)"
r="$repo/ai-generated/research"
export PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint
for item in no-late prefix early-profile-census alpha-two-debit alpha-two-live-cubic-beta-one; do
    m="$r/dirk11-thirteen-invisible-six-$item/sources.sha256"
    first="$(head -1 "$m")"
    if [[ "$first" == *"  ai-generated/"* ]]; then
        (cd "$repo"; sha256sum -c "$m")
    else
        (cd "$repo/ai-generated"; sha256sum -c "$m")
    fi
done
(cd "$r/dirk11-thirteen-invisible-six-alpha-two-debit"; python3 project.py)
(cd "$r/dirk11-thirteen-invisible-six-alpha-two-live-cubic-beta-one"; python3 coordinate-audit.py)
python3 replay.py "$repo" --count adjacent
python3 replay.py "$repo" --count middle
