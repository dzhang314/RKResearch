#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
input_arg=proof-inputs
if [ "$#" -gt 0 ]; then input_arg="$1"; fi
input="$(cd -- "$input_arg" && pwd)"
run() {
    local mode="$1" idx="$2" guard="$3"
    if [ "$mode" = regular ]; then
        python3 regular.py --p 0 --verify-over "$input/$mode/joint.txt" \
            --verify-prime 103 --rank-factor "$idx" --rank-guard "$guard" \
            --rank-file "$input/$mode/G-$guard.txt"
    else
        python3 singular.py --branch "$mode" --p 0 --verify-over "$input/$mode/joint.txt" \
            --verify-prime 103 --rank-factor "$idx" --rank-guard "$guard" \
            --rank-file "$input/$mode/G-$guard.txt"
    fi
}
run regular 0 old-norm
run regular 1 profile-ratio
run regular 2 c2
run F1 0 old-norm
run F2 0 old-norm
run Fn 0 old-norm
run Fn 2 c2
echo 'All seven literal Fn and singular guard fibers excluded.'
