# Rational DIRK order twelve in twenty stages

The literal tableau is ordinary lower triangular, with
\(A_{00}=0\), \(A_{11}=1/168\), and **twenty physical rows**.
Its exact rational order twelve is independently replayed on all
**7,813** unordered rooted trees through twelve. The scaled
thirteenth bush defect is \(97680781467/62269814438819680\).
The reduced numerators of that defect and the thirteenth tall
defect are coprime. Since their denominators divide powers of
the common literal tableau denominator \(D\) in the data, the
same tableau has **exact order twelve** over every nonzero
commutative ring inverting \(D\): both defects cannot vanish
there by integer Bézout. The two named diagonal entries are still
distinct because \(168\mid D\).

This improves the rational upper bound from 21 to 20, not the
15-stage real-algebraic optimum. The denominator includes primes
greater than twelve, so it does **not** improve the separate
factorial-only twenty-one-stage witness. It is an upper
construction, not a rational minimum. This packet has no
end-to-end Lean certificate yet.

## Opening and interpolation

The old bank has ten literal slots. Its port indices are \(0,5,6,7,8,9\)
(zero-based), and each port is pure through actual size six.
Ports 8 and 9 are pure through size seven. In physical order the
old clocks are
\[
 (0,\tfrac1{84},\tfrac1{42},\tfrac1{21},\tfrac4{35},
   \tfrac17,\tfrac27,\tfrac37,\tfrac47,\tfrac1{11}).
\]
Each old row uses the interpolatory weights on the donor
indices in the executable check. The first two nonzero old
ports at \(1/21,4/35\) are only size-five pure. The first
true size-six port at \(1/7\) uses both of them; its normalized
internal nodes \(1/3,4/5\) meet the additional degree-four
moment on the two-endpoint four-node rule. The penultimate
decoder port \(4/7\) uses its prior size-six ports \(1/7,2/7,3/7\)
and both endpoints, and gets one more paid moment by their
symmetry. The last port \(u=1/11\) uses the integrated
cardinal polynomials for the six actual decoder nodes.

Write \(\Pi\) for this \(P_5\) interpolation, \(E\) for suffix
evaluation, \(Jf(X)=\int_0^X f(V)\,dV\). For a tree \(t\) with
size \(n\), let
\(\rho_t(X)=nX^{n-1}/t!-\Pi\boldsymbol{\Phi}_t(A_{\rm old})\).
Every \(\rho_t\) vanishes at \(0\); they are zero through size six.
The exact size-seven span is
\[
 F_6=X(X-u)(X-z)P_3,\qquad u=1/11,\quad z=4/7.
\]
Indeed the last two ports are already size-seven pure; the
constructor verifies the four independent directions against the
48 actual size-seven rooted vectors.

## Scored grid and reverse payment

The scalar quadrature uses the old origin and eleven scored
suffix sites. Their **reverse** order is
\[
 \mathbf x=(1,2/11,4/11,3/11,6/11,7/11,8/11,9/11,10/11,
     26881/94316,1/11),\qquad \mathbf y=\mathbf1-\mathbf x.
\]
All interpolatory scalar weights, including the weight at zero,
are nonzero. The twelve-node rule has degree eleven; the
zero-site weight is assigned to the old origin.

Let \(\mathbf w\) be the weights in the reverse order, with
the origin excluded, and let \(Q\) be the nodal polynomial
of the ten proper \(x\) sites (excluding \(x=1\)). Define
\(\mathbf g\) to be zero at \(x=1\); at every proper site it is
a common affine numerator divided by \(w_i x_i Q'(x_i)\).
It follows from Lagrange partial fractions that
\[
  \langle \mathbf g,\mathbf x^k\rangle_{\mathbf w}=0
  \quad (1\le k\le8).
\]
The moved scalar site \(26881/94316\) is not fitted
numerically. At an early proper site \(x_i\), let \(Q_i^*\)
be the full twelve-node hull with that site omitted.
Then \(w_i x_i Q'(x_i)=I(Q_i^*)/(x_i-1)\). The values
\((1-x_i)^2 I(Q_i^*)\) must be affine across the three
early proper sites to set \(g_i=y_i^3/6\) there. Each
of those three integrals is affine in the one moved site;
their collinearity is one exact nondegenerate linear solve.
The code reconstructs this site and the affine numerator
with no approximations. The first three nonzero rows of
the actual reflected matrix are then trapezoids on the
reflected origin and the current node.

For the actual lower triangular reverse matrix \(L\), the
verified equations are
\[
 \begin{split}
 L\mathbf1&=\mathbf y,\qquad L\mathbf y=\mathbf y^2/2,\\
 L\mathbf y^2&=\mathbf y^3/3+\mathbf g,\\
 L\mathbf y^3&=\mathbf y^4/4+(3/2)\mathbf y\mathbf g,\qquad
 L\mathbf g=(1/2)\mathbf y\mathbf g.
 \end{split}
\]
The other equations are the \(\mathbf w\)-weighted pairings
of \(L\mathbf y^4-\mathbf y^5/5\) and
\(L(\mathbf y\mathbf g)\) with \(EF_6\), all zero.
The latter statement can equivalently use \(L(\mathbf x\mathbf g)\)
since \(L\mathbf g\) is already known. The actual combined
67-by-66 linear system uses exact Gaussian elimination,
has coefficient and augmented rank 53, and its solution is
checked entry-by-entry.

In the forward ordering, \(T\) is the reversed weighted
transpose of \(L\); the suffix-to-old cross block is
\((EJ-TE)\Pi\). For any raw tree input the suffix difference
from the ideal scalar primitive is propagated by \(T\), with
an added error \(-(EJ-TE)\rho_t\). The first such error is
at derivative grade seven, so no products of two errors
can occur through grade eleven. Hence every error in the
weighted output has the form
\[
 \langle W^*(L,\mathbf x)\mathbf1,EJ\rho_t\rangle_{\mathbf w}
 -
 \langle L W^*(L,\mathbf x)\mathbf1,E\rho_t\rangle_{\mathbf w},
 \qquad d+n-1\le10,
\]
with \(d\) the word length and \(n=|t|\). Here \(d\le4\)
since nonzero \(\rho_t\) start at size seven. The ideal scalar
parts cancel by integration by parts (all degrees at most
eleven, and both old error functions vanish at zero).
Actual reverse deviations at grades at most two are zero;
at grade three they lie on \(\mathbf g\), and at grade four
in the span of \(\mathbf g,\mathbf y\mathbf g\).
Their paid moment cancellations use degree at most eight
and seven respectively. At the very last reverse step
(grade five) the size constraint leaves only the actual
\(F_6\); precisely its two checked mixed pairings pay that step.
This accounts for all rooted shapes, independently of the
exhaustive integer replay.

The first forward suffix site is \(u\). Its full padded row
coincides with literal old row 9, and the constructor verifies
the full-vector equality before redirecting all uses and
adding its weight to the old port. In general, an implicit
duplicate can also differ by a shift between its own two
self-coordinate positions, because the original and duplicate
elementary vectors agree by induction on the rooted tree.
The computed shift here is zero. Thus the physical width is
\(10+11-1=20\), not a count of aggregate abscissae.

## Reproduction

Both the constructor and independent checker use the Python
standard library:

    python3 -B build.py --emit /tmp/dirk12-twenty-rebuilt.json
    cmp tableau20.json /tmp/dirk12-twenty-rebuilt.json
    python3 -B verify.py
    sha256sum -c sha256.txt

The checker does not import the constructor or its flagged
spaces. It enumerates canonical balanced-bracket rooted shapes
and evaluates them via exact integer-cleared matrix reads.
