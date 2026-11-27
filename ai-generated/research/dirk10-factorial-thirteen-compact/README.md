# Compact and native factorial-localized DIRK10 in thirteen stages

The [compact literal tableau](tableau13.json) gives **exact order ten in 13 diagonally implicit stages over every nonzero commutative ring with \(10!\) invertible**. The coefficients have at most ten numerator digits. Its common denominator is
\[
          D=1555848000=2^6 3^4 5^3 7^4\mid (10!)^4 .
\]
This is the same ten-site, rank-one, three-literal-merge architecture as in the [original 13-stage proof](../dirk10-factorial-thirteen-and-fourteen/README.md), but the free exact tap solution was reduced in its homogeneous lattice. The corrected values are independently checked against every cut equation. The [compact 14-stage alternative](tableau14.json) likewise admits just the factorial primes, and its common denominator 4200789600 also divides \((10!)^4\).

Both new literal matrices independently pass all 1,205 rooted conditions. The two eleventh-order defects are unchanged: \(179/279936\) for the bush and \(-9809/1049760\) for the tree with two leaf children and an eight-vertex bush child. The cleared denominators pay, and \(274(179)+5(-9809)=1\) proves exactness in every specialization, not just over \(\mathbb Q\).

## Full Lean theorem for width 13

The literal method is checked by graded normalized defect flags of dimensions \(0,0,0,1,2,4,7,9,10,11\). The reviewed sufficient-flag argument proves all ordinary rooted order conditions. Rational equality is converted to integer identities and then transported, so the extra rational flag-coordinate denominators are not assumed invertible in the target.

In **RKResearch.Certified.DIRK10FactorialThirteenFlagReplay**, the final declarations are:

- **transport**, the literal exact rooted order-ten payment after inverting \(D\).
- **next_star_defect** and **next_mixed_defect**, the two actual cleared eleventh-order relations over any ring with an inverse of \(D\).
- **exists_exact_factorial**, exact width-13 DIRK10 over any nontrivial commutative ring inverting \(10!\).
- **exists_exact_iff_factorial_unit**, the converse too: the tall-tree condition already implies that \(10!\) is a unit. This is a statement about existence at width 13, not a claim of minimality there.

The full compact thirteen-stage proof and typed audit check with Lean/Mathlib **4.36.0**, using only propext, Classical.choice, and Quot.sound. The core numeral module for the denominator and both next-order defects also passes without axioms on 4.34.1, 4.35.0 and 4.37.0-rc1. No full Mathlib pairing other than 4.36 is asserted. The compact fourteen-stage alternative is verified by exact arithmetic, not by these width-13 Lean declarations.

## Replay

From this directory:

    python3 -B audit_tableau.py
    python3 -B rebuild.py 13 --emit /tmp/dirk13-compact.json
    python3 -B rebuild.py 14 --emit /tmp/dirk14-compact.json
    cmp tableau13.json /tmp/dirk13-compact.json
    cmp tableau14.json /tmp/dirk14-compact.json

From ai-generated:

    p=research/dirk10-factorial-thirteen-compact
    tmp=$(mktemp -d)
    python3 -B research/dirk10-twelve-rational-flags/generate-flags.py "$p/tableau13.json" \
        "$tmp" --stem DIRK10FactorialThirteenFlagReplay
    for f in "$tmp"/*.lean; do cmp "$f" "lean/RKCert/ReviewedNative/$(basename "$f")"; done
    sha256sum -c "$p/sources.sha256"
    sha256sum -c "$p/dependencies.sha256"

From ai-generated/lean in the pinned environment:

    lake build +RKCert.ReviewedNative.DIRK10FactorialThirteen
    lake env lean AuditDIRK10FactorialThirteen.lean
