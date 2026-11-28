# Native finite-field certificate

The module `RKCert.ReviewedNative.ERK10SixteenF17` checks the
literal 16-stage method over \(\mathbb F_{17}\).
Its two checked endpoints are:

- `RKResearch.Certified.ERK10SixteenF17.order_ten`, on the
  actual finite-rooted-tree predicate, and
- `RKResearch.Certified.ERK10SixteenF17.exact_f17`, with
  strict explicitness and the actual failure of order eleven.

The reflective cache groups 487 stage profiles by grade and
value, computes 221 stage actions, and checks 985 joins.
All cache receipts are proved using kernel reduction.
The generic normalized-tree induction covers every reviewed
tree, regardless of binary presentation. The eleventh bush
has factorial-scaled output 3 rather than 1.

The two native endpoints were checked with Lean/Mathlib 4.36.0;
only standard axioms are reported. No claim is made here about
the native status of the higher prime-power construction or
about an all-toolchain dependency build.

From the adjacent Lean development with its matching dependencies:

    cd ../../lean
    lake build +RKCert.ReviewedNative.ERK10SixteenF17:olean

The untrusted cache can be regenerated from the literal:

    python3 -B generate_native.py --emit /path/to/RKCert/ReviewedNative \
      --modules /tmp/erk10-f17-modules.txt
    sha256sum -c native-sha256.txt

The generator writes the data and receipt shards. The separate
handwritten Core and endpoint prove their connection to ordinary order.
