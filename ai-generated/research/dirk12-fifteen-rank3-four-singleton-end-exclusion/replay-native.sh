#!/usr/bin/env bash
set -euo pipefail
here="$(cd -- "$(dirname -- "$0")" && pwd)"
source_dir="$(cd -- "$here/../../lean/RKCert/ReviewedNative" && pwd)"
if [ "$#" -eq 0 ]; then compiler=lean; else compiler="$1"; fi
compiler="$(readlink -f -- "$(command -v -- "$compiler")")"
build="$(mktemp -d)"
trap 'rm -rf -- "$build"' EXIT
mkdir -p -- "$build/RKCert/ReviewedNative"
cd -- "$source_dir"
"$compiler" --version
for suffix in SingletonUnitCore FourSingletonArithmetic ThreeSingletonArithmetic; do
  stem="DIRKOrderTwelveFifteen$suffix"
  LEAN_PATH="$build" "$compiler" -j 1 -o "$build/RKCert/ReviewedNative/$stem.olean" "$stem.lean"
done
