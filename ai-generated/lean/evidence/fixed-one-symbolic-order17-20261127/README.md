# Standard-axioms order-17 receipt: 58 fixed-one strict SDIRK stages

On Lean 4.36.0, the native theorem
`RKResearch.Certified.FixedOneOrder17.witness` establishes a
rational lower triangular tableau with 58 physical stages,
constant nonzero diagonal 1, the reviewed `HasOrder 17`, and
`¬ HasOrder 18`. It appends a virtual block to an unchanged
46-stage predecessor. Exactly 4 literal predecessor
copies are merged into their own earlier originals, reducing
62 virtual stages to 58 retained physical stages.
The new bank of 4 physical samples is simultaneously
certified pure through size 10. No stability claim is made.

The arithmetic uses the generated (U), (B), (mathbf w)
and exact low-grade matrix products. The reviewed order proof is
the generic symbolic moment induction. It does not enumerate
any set of size-17 tree conditions. This is a rational upper bound, down from 60,
not a new lower bound or a change to the unrestricted real-algebraic
upper endpoints.

## Replay from the repository root

```sh
repo="$PWD"
base="$repo/ai-generated/lean/evidence"
work="$(mktemp -d)"
cp "$base/fixed-one-symbolic-order13-20261127"/{Seed11Donors,Symbolic13Data,Symbolic13}.lean "$work/"
cp "$base/fixed-one-symbolic-order15-20261127"/{Seed13Fast,Stage15Data,Stage15}.lean "$work/"
cp "$base/fixed-one-symbolic-order17-20261127"/{Stage17,Stage17Data,Audit17}.lean "$work/"
python3 ai-generated/research/rooted-tree-gram/gen_lean.py \
  ai-generated/research/fixed-one-newton/tableau-11.json --graded \
  > "$work/Certificate11.lean"
cd ai-generated/lean
lake build RKCert.ReviewedNative.GramLocalPurity \
  RKCert.ReviewedNative.CausalCopyLocal RKCert.ReviewedNative.ProtectedTail
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$1"
  for mod in Certificate11 Seed11Donors Symbolic13Data Symbolic13 Seed13Fast Stage15Data Stage15 Stage17Data Stage17; do
    lean -j1 -o "$mod.olean" "$mod.lean" || exit
  done
  lean -j1 Audit17.lean
' _ "$work"
```

Generate the native sources and the full integer-scaled physical
fixture with
[`gen_higher.py --through 17`](../../../research/fixed-one-higher-odd/README.md),
using the frozen order-thirteen literal. Check the three files for
this target against `generated.sha256`. The older witnesses and
their native sources are not changed. These are compiler-and-kernel
receipts for 4.36.0; full replay on the other requested releases is
not claimed by this packet.
