# Kernel certificate for the literal width-15 ERK10 over F29

This certificate uses the unchanged [literal tableau](tableau.json).
Its strictly lower-triangular \(A\) satisfies the ordinary rooted-tree
condition through order ten. The eleven-vertex bush gives normalized
value 11, hence defect 10 with explicit inverse 3 in \(\mathbb Z/29\).

The statements in namespace
**RKResearch.Certified.ERK10FifteenF29** include:

- **order_ten**: the actual repository predicate HasOrder 10 A b.
- **exact_zmod**: ERK A, HasOrder 10 A b, and failure of order 11
  on the given 15 rows.
- **physical_failure_unit**: the defect on the actual normalized
  eleven-vertex bush is a unit, not merely a nonzero residue.
- **exact_of_hom**: the same tableau transfers to any nontrivial
  commutative ring admitting a unital map from \(\mathbb Z/29\).
- **exact_of_char**: the resulting exact order-ten upper bound for
  every nontrivial commutative ring of characteristic 29.

The untrusted generator groups the rooted-stage data into 676
normalized profiles, recomputes 310 matrix actions and 1,430 binary
joins, and emits small kernel-checkable receipts. The reviewed
generic forest-factorial induction proves coverage of every rooted
tree of order at most ten. The kernel checks the data by natural
modular arithmetic before coercion into the actual coefficient ring.
There is no reliance on an unchecked executable equality.

Lean/Mathlib 4.36.0 results are in [the axiom audit](lean-4.36-audit.txt).
A full dependency build on the other Lean versions is not claimed.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FifteenF29:olean

To regenerate the literal-derived modules in an existing empty
directory, run from this research directory:

    python3 -B generate_native.py --emit /tmp/erk10-f29-regen \
      --modules /tmp/erk10-f29-modules.txt

The generated module names are listed in [modules.txt](modules.txt).
The two hand-written templates are instantiated only by changing the
module name. From the repository root, verify the complete source
manifest:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-f29/native-sha256.txt
