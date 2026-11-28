#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT HUP INT TERM
"$LEAN" -o "$dir/ERK10FifteenPrimeGeometry.olean" ERK10FifteenPrimeGeometry.lean
for file in ERK10FifteenPrimeGeometryBatch*.lean; do
    LEAN_PATH="$dir" "$LEAN" "$file"
    printf '%s: %s\n' "$file" passed
done
