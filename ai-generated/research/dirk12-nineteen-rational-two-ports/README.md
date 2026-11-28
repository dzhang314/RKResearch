# Rational DIRK order twelve in nineteen stages

A literal **nineteen-stage** ordinary DIRK tableau has exact
rooted order twelve over \(\mathbb Q\). An independent
balanced-bracket integer replay checks all **7,813** rooted
shapes through twelve. The two distinct physical diagonals at
indices \(0,1\) are \(0,9/616\). The scaled thirteenth bush
defect is \(97680781467/62269814438819680\); its reduced numerator
and the reduced numerator of the thirteenth tall defect are
coprime. Each defect denominator divides a power of the common
literal denominator \(D\) recorded with the tableau. Their
integer Bézout identity proves exact order twelve over every
nonzero commutative ring inverting \(D\), even if one of the
defects vanishes individually. The two diagonals remain distinct
since \(3\) and \(616\) divide \(D\).

This improves the rational upper bound, including the
[preceding twenty-stage construction](../dirk12-twenty-rational-port-splice/README.md).
It does not establish a rational minimum or improve the
15-stage real minimum. The coefficient localization here
inverts primes greater than twelve; over an arbitrary ring
where only \(12!\) is known to be a unit, the separate certified
arithmetic upper is [twenty-one stages](../dirk12-factorial-midpoint-21/README.md).
This packet does not yet have an end-to-end Lean proof.

## Opening adjustment and actual rank debit

Use the same ten old rows and six size-six decoder ports
\(0,5,6,7,8,9\) as in the preceding twenty-stage certificate,
but now choose \(u=1/11\), \(z=6/11\) for the last and
penultimate port. Take the three old clocks for ports
\(5,6,7\) to be
\[
 (c_5,c_6,c_7)=z(9/14,1/2,5/14).
\]
They are symmetric about \(z/2\), so the interpolatory
quadrature at \(z\) on \(0,c_5,c_6,c_7,z\) is exact
through degree five. This pays literal size-seven purity
at old port 8. Port 9 uses the degree-five primitive on
the six decoder nodes and is also size-seven pure.
All six named ports remain pure through size six, checked
on every rooted vector of those sizes.

The new ratios also make an exact dependency among the
remaining three size-seven port errors. To see why this
is a physical rather than fitted scalar rank, scale \(c_5\)
to one. The two earlier size-five-pure donors have clocks
\(a=1/3\) and \(b=4/5\). The three size-six-pure ports now
have clocks \(1,7/9,5/9\). Their rows use only zero, the
two donors, the first true port, and their own diagonal
as applicable. A size-seven tree with multiple root
children is already exact at such ports, since all its
children have size at most five. The remaining unary
child has size six. Its port residual is a linear
combination of:
1. the degree-five scalar primitive discrepancy
   \((A\mathbf c^5)_i-c_i^6/6\);
2. the literal tap \(A_{i,3}\) to the donor at \(a\);
3. the literal tap \(A_{i,4}\) to the donor at \(b\).

In fact the child is already pure through size six at
zero, at the earlier true port, and at the target port
itself. Only the two named donors can contribute its
deviations from the ideal scalar child profile. For the
selection of ratios, put \(P(X)=X(X-a)(X-b)(X-1)\);
\(JP(1)=0\) is the additional degree-four moment at
the first true port. At a later \(x\) the primitive
discrepancy is \(x JP(x)-J(XP)(x)\) and the two taps are
\(J L_a(x)-[JP(x)/P(x)]L_a(x)\), and the same formula
with \(L_b\), for the four-donor cardinals. In this
weighted three-column determinant at clocks \(1,t,s\),
the additional factor is \(3s+3t-4\). Taking \(s=2t-1\)
for the five-site symmetry gives \(t=7/9,s=5/9\).
The selection does not require the determinant formula
to be trusted: the exact three literal rows of these
columns are checked to satisfy
\[
 R_7=(3875/8019)R_5+(2000/3773)R_6,
 \qquad \operatorname{rank}(R_5,R_6)=2.
\]
Scaling back to \(c_5=27/77\) only rescales the columns and
preserves this relation.

Write \(\Pi\) for interpolation on the six actual ports,
\(J f(X)=\int_0^X f\), and
\(\rho_t(X)=|t| X^{|t|-1}/t!-\Pi\boldsymbol{\Phi}_t(A_{\rm old})\).
The \(\rho_t\) are zero for \(|t|\le6\), and all vanish at zero.
The literal size-seven residual space \(F_6\) is now exactly
the three-dimensional subspace of \(P_6\) defined by
\[
 f(0)=f(z)=f(u)=0,\qquad
 f(c_7)=(3875/8019)f(c_5)+(2000/3773)f(c_6).
\]
The first three vanishing constraints are physical pure ports.
The fourth follows from the donor rank debit; the exact
constructor finds three independent residuals among the 48
trees of size seven. This is the dimension used in the top
reverse pairings, not the four-dimensional space of
polynomials satisfying just the first three equations.

## Reverse solve, true merge and full order

The same grid as at twenty stages is used, but now its last
two reverse sites are \(u,z\). The first four reverse sites
remain \(1,2/11,4/11,3/11\); the rational freed site remains
\(26881/94316\). The complete reverse order is
\[
 \mathbf x=(1,2/11,4/11,3/11,7/11,8/11,9/11,10/11,
          26881/94316,1/11,6/11),\qquad \mathbf y=\mathbf1-\mathbf x.
\]
Assign the scalar origin weight to old row zero. With actual
nonzero proper weights \(\mathbf w\), let \(\mathbf g\)
be the affine-numerator barycentric cubic from the earlier
construction. It vanishes at the reflected origin and
annihilates positive \(\mathbf x\) powers through degree eight.
The leading three reverse trapezoids and the same literal
identities are used:
\[
 L\mathbf1=\mathbf y,\quad L\mathbf y=\mathbf y^2/2,\quad
 L\mathbf y^2=\mathbf y^3/3+\mathbf g,\quad
 L\mathbf y^3=\mathbf y^4/4+(3/2)\mathbf y\mathbf g,\quad
 L\mathbf g=(1/2)\mathbf y\mathbf g .
\]
Against the actual \(EF_6\), the two weighted pairings of
\(L\mathbf y^4-\mathbf y^5/5\) and \(L(\mathbf y\mathbf g)\)
are zero. The exact 64-by-66 system has coefficient and
augmented ranks 51. The fifth-grade condition no longer
tries to pay the extra fourth residual direction, which
would obstruct this two-port merge in the tested fixed chart.

The full-tree payment follows the earlier argument: take
\(T\) the reversed weighted transpose of \(L\) and cross
block \((EJ-TE)\Pi\). The first suffix derivative error is
at grade seven, so a product of two errors cannot occur
through grade eleven. Every term in the weighted error is
therefore a true word of length \(d\le4\) acting on a
single primitive injection of a residual \(\rho_t\), with
\(d+|t|-1\le10\). The scalar part cancels by integration by
parts and the degree-eleven quadrature. The actual reverse
words differ from their ideal polynomials first in
\(\mathbf g\) at grade three, then in
\(\operatorname{span}(\mathbf g,\mathbf y\mathbf g)\) at grade
four, giving the ordinary paid annihilations. At grade
five only \(EF_6\) is seen, and the exact mixed pairings
above finish it.

The first two forward suffix copies lie at \(z,u\).
Each old port row equals the degree-five integrated
cardinal row at its own site. For the earlier one,
the future \(u\) tap is literally zero by the symmetric
five-node rule; for the later one it is its defining
quadrature. The cross block thus gives exact raw row
identities with those two old rows, up to possible
internal-suffix-to-old port coordinate shifts. Such
shifts preserve true derivative vectors by induction
on trees, but do not even occur in this chosen solution:
all three so-called shifts are checked as zero. Both
entire padded rows are equal before redirecting every
use and adding the weights. The actual width is
\(10+11-2=19\).

## Reproduction

All checks use Python's standard library:

    python3 -B donor-rank.py
    python3 -B build.py --emit /tmp/dirk12-nineteen-rebuilt.json
    cmp tableau19.json /tmp/dirk12-nineteen-rebuilt.json
    python3 -B verify.py
    sha256sum -c sha256.txt

The independent replay of the final literal does not
import the constructor, flags, or contraction identities.
