# Dirt interpolation and a rational Jacobi obstruction

Use the actual full-mark width-ten data in the
[main packet](README.md). The first reverse row is the
live endpoint, \(D_4\) has dimension three, and \(V\)
has the exact two early witnesses proved there.
There are at least three distinct dirty clock labels
after the masked cuts. Let \(m\) count distinct
nonzero forward high labels, \(r_0\) the number of
physical high zeros, and \(e\) the number of
**additional** endpoint copies. Thus
\(10-m-r_0-e\) is the excess ordinary visible
multiplicity. The rational scalar anchor bound gives
\(m\ge7\).

## The new terminal test is only a linear dirt moment

Some actual zero-model combination through size five
has high response \(\boldsymbol\delta\), after scaling.
Its opening-origin entry is zero (a zero model,
and an actual explicit origin). All other old
weights vanish. Marking it by \(X^k\), \(0\le k\le5\),
still fits actual order ten, so
\[
             \sum_i w_i x_i^k \delta_i=0,\qquad 0\le k\le5.
\]
There is no early-null requirement on this chosen
zero-model combination: we are only multiplying
its root by clock marks, not transporting through
its old part. These are pure actual **linear dirt**
moments, distinct from the genuinely tilted words
of length five.

Consider two possible cofactor situations.

* A leaking \(D_2\) seed \(\boldsymbol u\) on
  eight effective visible labels \(T\), with
  exactly seven positive tests. It has aggregate
  \(U_z=L/[zA'(z)]\), with \(A(X)=\prod_{z\in T}(X-z)\)
  and \(L\ne0\). Its first two marks span \(D_4\).
  From \(\boldsymbol\delta,C\boldsymbol\delta\in V\),
  the aggregate of \(\boldsymbol\delta\odot\boldsymbol u\)
  has four zero ordinary moments (marks \(0,\ldots,3\)).
  The coefficient is therefore \(G(z)/A'(z)\)
  for some \(\deg G\le3\), by the same Vandermonde.
* A leaking \(D_3\) seed \(\boldsymbol h=K\boldsymbol u\)
  on seven effective visible labels \(T\), with six
  positive tests. Its aggregate is likewise
  \(H_z=L/[zA'(z)]\), \(L\ne0\).
  In the relevant charts
  \(D_4=\langle\boldsymbol u,\boldsymbol h,C\boldsymbol h\rangle\),
  so the aggregate of \(\boldsymbol\delta\odot\boldsymbol h\)
  has three zero ordinary moments (marks \(0,\ldots,2\)).
  Thus it too is \(G(z)/A'(z)\) with \(\deg G\le3\).

These marked dirt calculations are ordinary
interpolation: a vector on \(s\) distinct points
annihilating powers \(0,\ldots,k-1\) is an
interpolation cofactor times a polynomial of degree
at most \(s-k-1\). Apply the same formula with a
factor \(z\) for positive forward tests. The
“effective” set includes endpoint \(1\) only if
its pool is not forced zero by a unique initial
physical endpoint; otherwise the endpoint has
each true defect zero and is omitted. The exceptional
unprobed physical zeros do not enter the cofactor.

In either case the actual dirt at an ordinary
singleton equals the same polynomial
\[
                         \Delta(z)=zG(z)/L .
\]
If \(\boldsymbol u\) is pure and supported on an
ordinary opposed pair, \(\boldsymbol\delta\cdot
\boldsymbol u=0\) makes its two dirt values equal;
the aggregate of \(h\) there is nonzero, so their
common value is \(\Delta\) as well. If \(\boldsymbol u\)
is pure supported on a sole physical high zero,
\(\boldsymbol\delta\cdot\boldsymbol u=0\) makes
its dirt zero, again the value of \(\Delta(0)\).
No physical score is divided in any of these
conclusions.

## Three allowed exceptional site sets, all impossible

In the cases below, all departures from the
polynomial dirt \(\Delta=XG/L\) are confined to
a site set \(\mathcal E\) contained in one of
\(\{1,c\}\) for a single ordinary repeated clock
\(c\), \(\{0,1\}\), or \(\{1\}\). If \(G=0\)
then dirt is supported at at most two labels,
already impossible. Thus \(G\ne0\).

For every polynomial \(q\) of degree at most five
vanishing on \(\mathcal E\), the linear dirt
moments and scalar accuracy through degree nine
give \(I(XGq)=0\); the opening origin has
\(\Delta(0)=0\). If \(\mathcal E\subseteq\{0,1\}\)
choose \(q=X(1-X)G\) to get
\(\int_0^1 X^2(1-X)G^2=0\); if just \(\{1\}\),
one could also use \(q=(1-X)G\).
These nonzero squares have strictly positive
formal integral over \(\mathbb Q\).
For example a positive-definite moment Gram
matrix on cubics gives the same algebraic fact.
So these cases fail.

For \(\mathcal E\subseteq\{1,c\}\), choose
\(q=(1-X)(X-c)R\), \(\deg R\le3\).
Then \((X-c)G\) is a nonzero degree-at-most-four
polynomial orthogonal to all cubics with weight
\(X(1-X)\). That orthogonal line is spanned by
\[
                L_4(X)=42X^4-84X^3+56X^2-14X+1 .
\]
This follows by strict positivity on cubics
and four exact moment cancellations for \(L_4\),
replayed independently. It forces \(L_4(c)=0\).
For \(c=A/B\) in primitive integers, the
homogeneous polynomial modulo \(11\) is
\(9A^4+4A^3B+A^2B^2+8AB^3+B^4\);
it has no projective root.
The [portable scalar receipt](../../lean/RKCert/ReviewedNative/ERK10TiltJacobiFour.lean)
checks the finite integer moment and modulo-\(11\) gates.
Thus this final class also fails over the rationals.

## Where the cofactor and its exceptions come from

All cases below use only the earlier low-grade,
score-weighted proofs. In each such reuse the one
old ingredient needing pure length five was the
two forward witnesses for early contrasts; the
exact tilted prefix rank in the main packet replaces
that ingredient. No old terminal grade-five moment
is used. The additional marked dirt test above is
derived independently from the actual zero-model
source.

### Nine or ten distinct nonzero labels

Ten means all ten clocks distinct and nonzero. The
[paid fourth-distinct exit](../erk10-five-opening-nine-label-one-pair/TEN-DISTINCT.md)
is fully low-grade and rules it out.

For nine labels, a sole duplicate endpoint is
excluded by the
[paid early and later jump proof](../erk10-five-opening-nine-label-endpoint-repeat/README.md);
its separated first jump cannot find an interior
repeat. One high zero with otherwise distinct
clocks is excluded by the
[one-zero nine-visible low-grade proof](../erk10-five-opening-zero-high-largest/README.md).
In the remaining case there is a unique endpoint
and one ordinary visible pair. The
[aggregate-exact grade-two case](../erk10-five-opening-nine-label-one-pair/README.md#if-the-grade-two-aggregate-is-zero)
is ruled out by actual low reads, whether grade
three leaks or not. If grade two leaks, the eight
ordinary visible labels are the \(T\) of the first
cofactor situation. All ordinary singletons
have the polynomial dirt; the sole exceptions
are the pair and endpoint. Use the rational Jacobi
exit just proved. This avoids all later nonic
equations.

### Eight nonzero labels

The excess beyond eight distinct labels is two.

* With unique endpoint and no high zero, the
  multiplicity is one ordinary triple or two
  ordinary pairs. Grade two is pure on the seven
  ordinary groups. If grade three is pure, the
  old [single-label](../erk10-five-opening-eight-label-triple/README.md#no-grade-three-leakage)
  or [two-mode tracking](../erk10-five-opening-eight-label-pairs-zero/README.md#all-grade-three-aggregates-exact)
  grade-four argument already gives contradiction.
  Otherwise the grade-three cofactor is on the
  seven ordinary groups. Its mark and the pure
  \(\boldsymbol u\) saturate \(D_4\), so
  \(\boldsymbol u\) occupies a single label. The
  strict single-label proof there forces
  \(\boldsymbol h\) to leak (otherwise it is a
  multiple of \(\boldsymbol u\) vanishing at its
  first live point, and \(K u=0\) prevents the
  first different live label's required read).
  We are in the second cofactor situation.
  For a triple there is just one possible exceptional
  interior label. For two pairs the active
  \(\boldsymbol u\)-pair has equal dirt by its
  opposed mode and is not an exception, leaving
  the dormant pair. Both give the Jacobi exit.
* Unique endpoint, one high zero and one ordinary
  pair: the all-pure degree-three branch is the
  [two-mode low-grade proof](../erk10-five-opening-zero-high-repeats/README.md#if-grade-three-is-entirely-pure).
  If grade three leaks, \(\boldsymbol u\) is at
  one label, and \(\boldsymbol h\) is the seven-site
  ordinary cofactor, as above. If the active
  \(u\) is at the zero, dirt vanishes there and
  the dormant pair is the only ordinary exception.
  If active at the pair, its values equalize,
  leaving at most the high zero plus endpoint
  as exceptions. Both are excluded.
* Unique endpoint and two high zeros (no ordinary
  repeat), or a duplicated endpoint and one high
  zero (no ordinary repeat): the old
  [paid low-grade repeats proof](../erk10-five-opening-zero-high-repeats/README.md)
  already closes these branches, including the
  possible leaking grade two in the latter.
* Two endpoints and one ordinary pair (no high
  zero): if grade two is pure, the
  [pure-\(u\) late-endpoint contradiction](../erk10-five-opening-eight-label-endpoint-repeat/README.md#zero-grade-two-aggregate-the-late-endpoint-cannot-have-the-required-jump)
  uses only grades up to four. If it leaks,
  the eight-site set \(T\) includes the endpoint,
  and the first cofactor situation applies.
  Only the ordinary pair and endpoint are
  exceptional, giving the Jacobi exit.
* Three endpoints but no ordinary repeat or
  high zeros: the
  [three-endpoint eight-visible case](../erk10-five-opening-three-endpoint-repeats/README.md#count-and-the-three-endpoint-eight-label-branch)
  ends in the same early jump/causal contradiction
  at grade four.

### Seven nonzero labels

If the endpoint is unique, grade three is pure
on the six ordinary groups, and the old complete
[nonzero-high seven-label proof](../erk10-five-opening-triple-pair/ZERO-TRIPLE-POOL.md#combined-seven-label-conclusion)
or [seven-visible high-zero argument](../erk10-five-opening-zero-high-seven/README.md#unique-endpoint-permanent-one-coordinate-donors-and-a-full-two-coordinate-invisible-group)
already closes it. All those proofs are low-grade.

If the endpoint repeats and grade three is still
pure on all seven visible groups, the old
[exact-grade-three endpoint proof](../erk10-five-opening-seven-label-endpoint-repeat/README.md)
and its
[three-endpoint](../erk10-five-opening-three-endpoint-repeats/README.md)
and [high-zero](../erk10-five-opening-zero-high-seven/README.md)
variants use only the grade-four two-target square,
strict nilpotent argument, or corrected cubic.
They apply here by the actual off-prefix witnesses.

It remains repeated endpoint **and** grade-three
leakage. Grade two is pure (seven positive
tests). The same one-label and strict nilpotence
argument makes \(\boldsymbol h\) itself leak,
and puts \(D_4=\langle u,h,Ch\rangle\) in vector
notation. In particular \(\boldsymbol h\) has
the seven-visible cofactor including endpoint and
the second polynomial-dirt situation applies.
Nonzero \(\boldsymbol u\) is supported at one
nonzero reverse ordinate (not endpoint).
The possible exceptions are counted as follows:

* No high zero and two endpoints: among the
  ordinary sites there is one triple or two pairs.
  In the latter case the one active ordinary
  pair equalizes its dirt, leaving only the
  dormant pair. Thus at most one ordinary
  exception besides endpoint.
* One high zero and two endpoints: there is one
  ordinary pair. If the active label is the
  sole zero, its dirt is zero and the pair
  may be the only ordinary exception. If active
  at the pair, it equalizes and the high zero
  may be exceptional. Either gives one of the
  allowed sets above.
* Two high zeros and two endpoints: all ordinary
  sites are singletons, so just potential origin
  and endpoint exceptions.
* Three endpoints with no high zero leave one
  ordinary pair. It must be active for the nonzero
  \(\boldsymbol u\), so it equalizes. Three endpoints
  and one high zero leave only ordinary singletons.
  Four endpoints and no high zero give no
  nonendpoint pure \(u\)-support at all, impossible
  at its first live nonendpoint.

Every allowed case therefore has either a single
ordinary exceptional label plus endpoint, or only
\(0,1\). The Jacobi and square exits above close
both. This exhausts the full-mark branch.
