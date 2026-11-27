# Reusable even moment tail and actual exact order-12 witness

The standard-axioms Lean theorem
`RKResearch.Certified.EvenTerminal12.witness` certifies exact order 12
in 28 rational strict SDIRK stages, with literal common diagonal (1/4).
Its proof computes only finite matrix and scalar receipts at the even
target; it does not enumerate any order-12 rooted trees. Its certified
preparation is order 10 in 22 stages, and the five actual old donor
rows are proved locally exact through size six before constructing
the tail. The virtual 33-stage object is quotiented by actual equality
of entire strict rows with separate self taps.

## Replay from repository root

```sh
repo="$PWD"
res="$repo/ai-generated/research/even-terminal-head-sharing"
ev="$repo/ai-generated/lean/evidence/even-moment-tail-20261127"
work="$(mktemp -d)"
cp "$ev"/{Seed10Even,Even12Data,ProofEven12,Audit12}.lean "$work/"
python3 ai-generated/research/rooted-tree-gram/gen_lean.py "$res/tableau-10.json" --graded \
  > "$work/Certificate10.lean"
(cd "$work" && sha256sum -c "$ev/sources.sha256")
cd ai-generated/lean
lake build RKCert.ReviewedNative.GramLocalPurity \
  RKCert.ReviewedNative.GeneralMomentTail RKCert.ReviewedNative.CausalStageMerge \
  RKCert.ReviewedNative.ProtectedTail
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$1"
  for mod in Certificate10 Seed10Even Even12Data ProofEven12; do
    lean -j1 -o "$mod.olean" "$mod.lean" || exit
  done
  lean -j1 Audit12.lean && leanchecker -v ProofEven12 Seed10Even
' _ "$work"
```

The typed import audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for the actual witness,
the copied-row identity and the certified old donor observations.
The full proof is checked on Lean/Mathlib 4.36.0. Compilation of the
new target module took 11.46 s after the compiled preparation and
data; the order-10 preparation's Gram certificate took 3m36.62s.
The proof generation and the physical rational files regenerate
byte-for-byte. No other Lean toolchain or full higher even Lean
replay is asserted in these receipts.
