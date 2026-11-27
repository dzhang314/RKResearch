# Twelve DIRK10 stages with only five extra denominator primes

The [literal tableau](tableau.json) has exact order ten in 12 ordinary unequal-diagonal DIRK stages whenever
\[
 D=14762353142762908220160000000
   =2^{14}3^7 5^7 7^2 47^3\,83\,97\,199\,647
\]
is invertible in a nonzero commutative ring. Thus a single width-twelve tableau is available over \(\mathbb Z[1/(210\cdot47\cdot83\cdot97\cdot199\cdot647)]\), with only **five primes beyond the factorial localization**. Over this subring of \(\mathbb Q\), 12 is minimal by extension of any smaller tableau to \(\mathbb Q\) and the rational lower bound. This is not an endpoint over \(\mathbb Z[1/210]\) itself or a minimality statement over other rings.

Compared with the [original twelve-stage rational tableau](../dirk10-twelve-rational-three-ports/README.md), this has a smaller prime support. The exceptional supports above the factorial primes are disjoint. There is no new assertion of unconditional characteristic-zero gluing.

## Construction and exactness

Use the centered proper symmetric parameters \((\alpha,\beta,\gamma)=(2/5,2,2/3)\), with the center and both endpoints included. Their scalar order-nine precision is paid, and the right-endpoint weight is \(97/1890\). The seven opening clocks are
\[
        (0,1/8,1/4,u=1/2,p=112/423,q=-1/2,r=1/6).
\]
The rank-one construction is the same literal cross mechanism as in the original width-twelve proof. The forbidden future coefficient in row \(q\) vanishes at this \(p\). The reverse order is
\[
        (1,7/10,3/10,3/2,5/6,1/6,-1/2,1/2).
\]
The first three weights are units on the stated localization. Use the raw transpose with cubic cofactor density, so the later individual weight numerators need not be units. The top response system has Smith entries \(1,1,1620,311040,1555200,0\) after paid row denominator/content clearing; it is consistent of rank five, with all its nonzero entries factorial units. The standalone regeneration checks the actual supplied rational solution of the six top equations, all 31 reflected injection-word tests, and the three complete padded row equalities. The count is \(7+8-3=12\) on the actual rows.

The independent literal checker pays all **1,205** rooted conditions. The normalized eleventh bush and the tree with two leaf children plus an eight-vertex bush child have defects
\[
          -1207/5184000,\qquad 2711/3888000 .
\]
Both denominators divide \(D^2\); the exact identity \(1141(-1207)+508(2711)=1\) rules out order eleven in every nonzero denominator-unit ring, including characteristics where one of these two tests vanishes.

## Reproduction and native proof

    python3 -B audit_tableau.py
    python3 -B rebuild.py --emit /tmp/dirk12-five-rebuilt.json
    cmp tableau.json /tmp/dirk12-five-rebuilt.json

The complete Lean/Mathlib **4.36.0** certificate **RKResearch.Certified.DIRK10FiveExtraTwelveFlagReplay.exists_exact_of_unit** transports the reviewed order predicate from its rational flag proof to integer identities and specializes only the literal denominator. The two distinct next defects and their Bézout combination are checked in the target ring. The typed audit lists only propext, Classical.choice and Quot.sound.

From ai-generated:

    p=research/dirk10-twelve-five-extra-primes
    tmp=$(mktemp -d)
    python3 -B research/dirk10-twelve-rational-flags/generate-flags.py \
        "$p/tableau.json" "$tmp" --stem DIRK10FiveExtraTwelveFlagReplay
    for f in "$tmp"/*.lean; do cmp "$f" "lean/RKCert/ReviewedNative/$(basename "$f")"; done
    sha256sum -c "$p/sources.sha256"

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.DIRK10FiveExtraTwelve
    lake env lean AuditDIRK10FiveExtraTwelve.lean
