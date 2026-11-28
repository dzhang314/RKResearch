#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
test "$#" -eq 1
guard_dir=$(cd -- "$1" && pwd)
compact=../dirk11-thirteen-invisible-six-cubic-compact-projection
g5=$compact/gamma5-guard-support.txt
pair=pair-guard-support.txt
python3 check-jacobi-guards.py "$g5" "$pair" "$guard_dir"
run() {
    local chart=$1 support=$2 idx=$3 kind=$4 file=$5
    shift 5
    python3 rank.py --p 0 --chart "$chart" --no-extra \
        --verify-over "$support" --verify-prime 103 --rank-factor "$idx" \
        --rank-guard "$kind" --rank-file "$guard_dir/$file" "$@"
}
for chart in five pair; do
    if [ "$chart" = five ]; then support=$g5; else support=$pair; fi
    run "$chart" "$support" 2 f3-lead 'GF3 degree.txt'
    run "$chart" "$support" 4 ip-V 'GI(P)(V).txt'
    run "$chart" "$support" 5 f3-disc-v 'GF3 discriminant V.txt'
    run "$chart" "$support" 6 det-m 'Gdet m.txt'
done
run five "$g5" 7 carrier-edge 'GU at 1 or B.txt'
run pair "$pair" 7 ell-V 'Gell V numerator.txt' \
    --second-guard "$guard_dir/Gfirst gap leader.txt"
echo 'All exact projection support factors excluded in both charts.'
