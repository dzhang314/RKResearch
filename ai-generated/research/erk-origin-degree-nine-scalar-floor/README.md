# Origin-only rational degree-nine quadrature needs at least seven sites

A degree-nine quadrature rule for uniform integration on \([0,1]\)
with rational abscissae cannot use a *possible* support of at most
six sites containing 0. The endpoint 1 need not be a site.
Weights may be signed or zero. This statement also holds over
the fraction field of a characteristic-zero discrete valuation
ring with uniformizer 2, with arbitrary residue field.
It is not a claim over unrestricted coefficient fields.

## Four cleared nodal moments and a parity contradiction

Pad any smaller support to an origin and five additional distinct
sites, assigning zero weights to the padding. Write the other
abscissae as reduced rational fractions \(u_i/v_i\), or as primitive
pairs in the valuation-ring version. Set
\[
 P(X)=\prod_{i=1}^5(v_iX-u_i)=\sum_{i=0}^5 a_i X^i .
\]
No factor becomes the zero polynomial modulo 2.
Exactness applied to \(X^jP(X)\) for \(j=1,2,3,4\) requires
all four integrals to vanish: these polynomials vanish at the
entire support and have degree at most nine.
After multiplying their coefficient vectors by their least common
denominators, the four integer rows (ascending in \(a_i\)) are

    (210, 140, 105,  84,  70,  60)
    (280, 210, 168, 140, 120, 105)
    (630, 504, 420, 360, 315, 280)
    (504, 420, 360, 315, 280, 252).

Modulo 2 these require \(a_2,a_5,a_4,a_3\) to vanish.
The product remains nonzero over the residue field, so its
degree at most one forces at least four of the five slopes \(v_i\)
to be even. Every term of \(a_3,a_4,a_5\) therefore contains at
least two even slopes, hence those coefficients vanish modulo 4.
The second row modulo 4 now says \(2a_1=0\), so \(a_1\) is even too
(cancelling only one uniformizer 2 in the valuation ring).
The reduced product is constant; all five slopes are consequently
even. Every term of \(a_2\) is then divisible by four.
The first row modulo 4 is \(2a_0+a_2+2a_4=0\), which forces
\(a_0\) even. Now every coefficient vanishes modulo 2, contradicting
nonzero primitive reduction. No archimedean sign argument is used.

For the valuation-ring version it is enough to choose projectively
primitive coordinates for each field element; multiply its numerator
and denominator by a suitable power of the uniformizer. The same
modulo-2 degree count holds in any residue field, not just
\(\mathbb F_2\).

## Independent arithmetic

The [exact replay](exact-audit.txt) reconstructs the four cleared
rows and checks all normalized projective factor multisets over
\(\mathbb Z/2\) and \(\mathbb Z/4\). There are three surviving
mod-2 shapes and no mod-4 shapes. The Lean Core receipt checks the
three mod-2 shapes and all their normalized mod-4 lifts.
Its finite enumeration is a redundant rational arithmetic check;
the structural valuation-ring proof above uses no residue-field
enumeration.

    python -B audit.py
    # From the repository root: sha256sum -c ai-generated/research/erk-origin-degree-nine-scalar-floor/sources.sha256

To run the [Core receipt](../../lean/RKCert/ReviewedNative/ERKOriginDegreeNineMod.lean), use the corresponding standalone Lean compiler.
The quadrature-to-parity reduction itself is argued above.
