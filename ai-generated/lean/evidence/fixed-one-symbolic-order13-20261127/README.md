# Symbolic 35-stage fixed-one strict SDIRK order-thirteen receipt

`RKResearch.Certified.FixedOneOrder13.witness` proves the exact
rational order-thirteen upper bound in the reviewed `HasOrder`.
The virtual tableau is reindexed, then the actual 38-to-35 causal
quotient of exact predecessor duplicates is checked. This is not
a rooted-tree enumeration.

## Reproduce the build

From the repository root, using the reviewed Lean/Mathlib 4.36.0
project and the unchanged prior Gram witness:

```sh
repo="$PWD"
ev="$repo/ai-generated/lean/evidence/fixed-one-symbolic-order13-20261127"
work="$(mktemp -d)"
cp "$ev"/{Seed11Donors,Symbolic13Data,Symbolic13,Audit}.lean "$work/"
(cd "$work" && sha256sum -c "$ev/sources.sha256")
python3 ai-generated/research/rooted-tree-gram/gen_lean.py \
  ai-generated/research/fixed-one-newton/tableau-11.json --graded \
  > "$work/Certificate11.lean"
cd ai-generated/lean
lake build \
  RKCert.ReviewedNative.CausalStageMerge \
  RKCert.ReviewedNative.GramLocalPurity \
  RKCert.ReviewedNative.TailMatrixReceipts
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$1"
  for module in Certificate11 Seed11Donors Symbolic13Data Symbolic13; do
    lean -j1 -o "$module.olean" "$module.lean" || exit
  done
  lean -j1 Audit.lean && leanchecker -v Symbolic13 Seed11Donors
' _ "$work"
```

The generated `Certificate11.lean` must match the source digest
in the [original Gram receipt](../rooted-tree-gram-fixed-one-20261127/generated-source.sha256).
`Seed11Donors.lean` imports the already certified integer Gram trace
in implementation mode (with `import all`); the old certificate
source, proof and literal are unchanged. It proves localized
pure-row facts that were not part of that prior audit.

The original complete compile of `Symbolic13.lean` took 13.48 seconds
once its dependencies and p11 donor proof were available. The typed
audit checks the existential statement and lists the transitive
axioms of the final witness, an actual-copy identity, and one
localized seed proof. Only the standard axioms are used. The
recorded runs establish 4.36.0 compatibility; other Lean releases
are not asserted by this receipt.
