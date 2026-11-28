#!/usr/bin/env bash
# Use the pinned ai-generated/lean toolchain and its matched Mathlib cache.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
generated="$(cd "$here"/../.. && pwd)"
tmp="$(mktemp -d)"
trap 'rm -f "$tmp/DIRK12FactorialTwentyFlagData.lean"; rmdir "$tmp"' EXIT
python3 -B "$here/generate-integer-flags.py" "$here/tableau20.json" "$tmp"
cmp "$tmp/DIRK12FactorialTwentyFlagData.lean" \
  "$generated/lean/RKCert/ReviewedNative/DIRK12FactorialTwentyFlagData.lean"
cd "$generated/lean"
while IFS= read -r module; do
  lake build "$module"
done < "$here/native-modules.txt"
lake env lean "$here/native-audit.lean"
