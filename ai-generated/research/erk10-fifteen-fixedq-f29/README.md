# A literal 15-stage fixed-q ERK10 tableau in characteristic 29

The [literal tableau](tableau.json) is strictly
explicit and has exact order ten over
\(\mathbb F_{29}\). It is one fully regular
survivor of the fixed-\(q\) ordinary-pair
projective census, not a rational construction.
Its eleven reclassified raw reverse clocks are
\[
                      0,11,20,2,2,26,27,7,6,22,15
                                     \pmod{29}.
\]
The selected scalar cofactor is in the
\(A(1)=0\) branch in reverse coordinates.
This is a **15-stage upper bound**, with
no new stage minimum claim.

The independent integer replay checks the
literal lower triangle, clock sums, actual
fixed-\(q\) old decoder, and each of the
1,205 rooted order conditions through ten.
The normalized order-eleven bush has
defect \(11\boldsymbol b^T\boldsymbol c^{\odot10}-1
=10\) in \(\mathbb F_{29}\); the ordinary
unnormalized difference is \(22\).
The inverse of the normalized defect is \(3\).

For every **nonzero commutative ring of
characteristic \(29\)**, map the integer
representatives of this tableau via the
canonical homomorphism
\(\mathbb F_{29}\rightarrow S\).
Every normalized rooted condition is a
polynomial equality in the actual entries,
so is preserved by that homomorphism.
The same next-tree defect remains a unit:
\(10\cdot3=1\) in every such ring. Thus the
literal image has exact order ten there too,
with the actual denominators through eleven
paid by characteristic \(29\).
No prime-power lift or characteristic-zero
claim is made by the literal fixture alone.

## Exact replay

    python3 -B verify.py | diff -u exact-audit.txt -

From this overlay or repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-f29/sources.sha256
