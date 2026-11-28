# Native order-ten certificates over four small prime fields

Each `RKCert.ReviewedNative.ERK10SixteenF<p>` module proves the
ordinary rooted-tree order conditions for its literal strict
sixteen-stage tableau over `ZMod p`. Inside the matching namespace
`RKResearch.Certified.ERK10SixteenF<p>`, the theorem `order_ten`
proves `HasOrder 10 A b`, and `exact_f<p>` also proves strict
explicitness and failure of `HasOrder 11 A b`. Here `p` is
11, 13, 19 or 23. The normalized order-eleven bush outputs are
0, 6, 12 and 16, respectively, instead of 1.

The module `RKCert.ReviewedNative.ERK10PrimeFieldTransfer` also proves
that the four exact tableaux and the prime-17 tableau transfer to
every nonzero commutative ring of the corresponding characteristic.
The proof uses the injective prime-field embedding to transport the
order-ten equalities and preserve the order-eleven failure.

These are end-to-end checks on Lean/Mathlib 4.36.0. The
source receipts reuse the prime-17 normalized rooted-tree induction
with no prime-17 tableau data. Each profile, stage action, join, and
order payment is checked on its own literal prime field. The
[p-adic lifts](README.md) remain mathematical constructions with
exact arithmetic replays, not native `HasOrder` proofs.

From the adjacent Lean project with its matching dependencies:

    cd ../../lean
    for p in 11 13 19 23; do
      lake build "+RKCert.ReviewedNative.ERK10SixteenF${p}:olean"
    done
    lake build +RKCert.ReviewedNative.ERK10PrimeFieldTransfer:olean

To regenerate the data and receipt shards in an empty scratch directory,
run from this research packet:

    python3 -B generate_native.py \
      --emit /tmp/erk10-native-shards \
      --manifest-dir /tmp/erk10-native-manifests \
      --template-dir ../../lean/RKCert/ReviewedNative

The manifests list the 73 sources per prime, including the
core and endpoint. The hashes are relative to the repository root.
