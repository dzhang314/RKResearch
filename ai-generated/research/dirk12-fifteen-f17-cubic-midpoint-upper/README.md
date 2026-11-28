# A literal 15-stage order-twelve DIRK method over the cubic field of size 4913

The exact tableau in [tableau.json](tableau.json) is an **ordinary DIRK** method over
\[
            K=\mathbb F_{17}[z]/(z^3+7z^2+3z+10).
\]
Coefficients are the three residues from constant through quadratic. The cubic has no residue root and is irreducible. This is one selected field component of the midpoint nine-site early-return chart, **not** a product ring or a characteristic-zero construction. The field branch uses one of two linear orientation roots in \(K\); no further extension is required. Its physical pair split is one half, its ordinary first nonzero live clock is \(1/2\), and its normalized hidden four-stage clock list is \((1/4,1/3,8/11,1)\).

The literal tableau is lower triangular, has zero initial and final diagonals and has nonzero implicit diagonals. Thus it is not ERK or strict SDIRK. Its four zero output weights are physical stages 2–5. Its exact scalar and rooted order do not establish any real order or real stage-count improvement.

    python3 -B replay.py

The independent standard-library verifier reads the literal coefficients only, checks cubic irreducibility and true stage row sums, and verifies every unordered non-plane rooted tree through order twelve. The individual counts are \(1,1,2,4,9,20,48,115,286,719,1842,4766\). The order-thirteen star has scaled nonzero residual \(11+7z+12z^2\), so the field method has exact order twelve. No Lean theorem for this literal is asserted here.

A separate [canonical-multiset replay](independent-replay.py) checks
the same literal with independent direct cubic arithmetic through
all 7,813 conditions and checks the next-order defect. See its
[output](independent-replay.txt). The [uniform paid-ring lower
bound](../../lower-bounds/paid-beta/DIRK-PAID-GRADE-SIX.md) is also
15 at order twelve, so the stage count is sharp over this field.
Base change to any nonzero commutative algebra over this field
preserves the equations and the nonzero defect, because the latter
is a unit. This does not imply a smaller field or characteristic-zero witness.
