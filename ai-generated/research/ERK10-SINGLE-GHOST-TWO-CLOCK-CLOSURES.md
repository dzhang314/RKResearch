# Two outgoing clock labels at an invisible ghost: exactly six active taps remain

Work over a characteristic-zero field in the
[single invisible ghost chart](ERK10-SINGLE-INVISIBLE-GHOST.md),
with \(r=Ae_2\) supported on exactly two live numerical clocks
\(\alpha,\beta\). Let \(G=(X-\alpha)(X-\beta)\), \(T=G(c)-G(c_2)e_2\),
and use \(z\) for the actual grade-four complement defined there.
A **clean row** here is a live row with \(r_i=0\). It is
**effective for the mask** when \(G(c_i)\ne0\); this is a physical
condition, not an effective pooled weight assumption.

**Result.** The outgoing column cannot have seven, eight, or nine
active physical rows; it has exactly **six**, in groups of sizes
**four and two**. The group of two is a uniform opposing pair.
The group of four either has four distinct nonzero amplitudes or
has two opposing equal-amplitude pairs that already split in
grade four. The ordinary pooled output measure is exactly the
six-point Lobatto measure, but the seven clean physical rows have
five or six distinct clocks, not necessarily all Lobatto.
No exclusion of the remaining six-active-tap geometry, of other
outgoing clock counts, or of arbitrary fourteen-stage order-ten
tableaux is claimed.

## A. Grade-five endpoint models and bidirectional linear primitives

The base packet proves
\[
 F_4=\langle e_2,r,Cr,z\rangle,\qquad
 F_5=F_4+CF_4=\langle e_2,r,Cr,z,Cz\rangle,\qquad
 B(F_4|_I)=V_3|_I .
\]
Here \(I\) is the live index set and \(B\) on it is the nondegenerate
diagonal pairing. The last equality implies \(e_1\in E_5\),
since every \(F_4\) vector vanishes at the origin. The
[equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
already gives \(e_{14}\in E_5\) and \(e_{14}\notin E_4\).
Both physical ends are point exact through grade five in the
**forward** chart: the origin is exact in all grades, while at
the terminal row all of \(F_4\) vanishes, hence so does \(CF_4\).

Write
\[
 L=42X^4-84X^3+56X^2-14X+1,\quad H=XL,\quad \bar H=(1-X)L .
\]
The actual model of \(e_{14}\) is \(30b_{14}H\), so point
exactness forces \(b_{14}=1/30\).
For \(e_1\) the five scalar moments of its model through test degree
four are \(b_1\) times evaluation at zero. The model of \(e_1\)
and \(30b_1\bar H\) therefore differ by a polynomial of degree at
most five orthogonal to \(\mathcal P_{\le4}\) and vanishing at 1
(use terminal point exactness on \(e_1\)).
Factoring \(1-X\) and using the nonsingular weighted moment matrix
makes that difference zero. Evaluation at the origin fixes \(b_1=1/30\).
Consequently
\[
       e_{14}-H(c),\quad e_1-\bar H(c)\ \in F_5 .             \tag{A}
\]

Every actual reverse **polynomial** primitive difference through
grade five belongs to \(F_5|_I\).
Indeed the row
\(bY^k A-bY^{k+1}/(k+1)\) for \(k\le4\) annihilates \(E_4\) (paid
\(k+1+4\le9\)) and has zero terminal coordinate by strictness.
The terminal-zero part of \(\operatorname{Ann}(E_4)\) has dimension
four: \(E_4\) has rank nine and does not contain \(e_{14}\).
It is exactly \(B F_5\), whose rank is four since the sole ghost
indicator already lies in \(F_5\). These rows vanish at the ghost,
so their live normalization is the genuine polynomial primitive
difference in the actual live reverse matrix \(A^\vee\).
This uses neither the nonlinear reverse grade-five defect space nor
reverse order ten.

Define, now and below only over the clean rows,
\[
  \lambda_x=\sum_{i:\ c_i=x} b_i G(x)z_i .
\]
The actual products \(T\,C^k z\) for \(0\le k\le3\) are pure
and paid through grade nine. Hence
\[
             \sum_x x^k\lambda_x=0\quad(0\le k\le3).           \tag{Z}
\]
On any clock with \(\lambda_x=0\), multiplying (A) by the
clean mask and taking the pooled read shows
\[
 \begin{split}
  G(x)\big(b_{14}{\bf1}_{x=1}-H(x)\omega_x\big)&=0,\\
  G(x)\big(b_1{\bf1}_{x=0}-\bar H(x)\omega_x\big)&=0 ,
 \end{split}                                                \tag{E}
\]
where \(\omega_x\) is the sum of the clean output weights at \(x\).
At a singleton effective internal clean clock with \(\lambda_x=0\),
we have \(z_i=0\) and \(L(x)=0\), by the actual scalar model (A).
An effective clean endpoint with only one extra occurrence
cannot have \(\lambda_x=0\): (E) would force the extra row's
nonzero output weight to vanish.

We use two elementary quadrature facts. If the potential ordinary
support is contained in **at most six distinct sites including both
endpoints**, it is exactly the six-point Lobatto rule.
Indeed the product of the interior factors is nonzero; if it has
degree at most three, exactness against \(X(1-X)\) times its
multiples contradicts the nonsingular Beta matrix. If it has degree
four, those same four tests determine \(L\).
Conversely the canonical six-point rule is exact through degree
nine: divide by \(X(1-X)L\), and integrate the degree-at-most-five
interpolating remainder; all quotient terms vanish by its
orthogonality. Every canonical weight is nonzero. For instance over
the real splitting field these weights are strictly positive by
testing \(X(1-X)\) times the product of the squared other interior
factors at an interior node, and by the anchored endpoint moment
test for the endpoints. All coefficient and weight identities
transfer to arbitrary characteristic-zero splitting fields.
One may also obtain \(1/30\) for each canonical endpoint directly
by integrating \(H\) and \(\bar H\).

## B. No effective clean quartic residue on a small clean set

Suppose \(z\) vanishes at every effective clean row and there
are at most four distinct effective internal clean clocks.
There must be at least two such internal clocks: from
the paid G-weighted quadrature, putting the product of the
effective interior factors into the \(X(1-X)\)-weighted test
would otherwise make a nonzero polynomial of degree at most
three orthogonal to its own full degree range.

Let \(u\) be the first effective nonzero clean clock, and let
\(v\) be the last effective clean clock different from 1.
In the forward chart \(CT,C^2T\) vanish at all predecessors
of the contact at \(u\); at \(u\) the primitive errors through
five vanish. In the reverse chart the reflected polynomial
masks \(YG(c_I),Y^2G(c_I)\) give the same two assertions at
reflected clock \(w=1-v\), by the **linear** result in §A.
Writing \(G=X^2-SX+P\), the first two formal integrals at \(u\)
give \(5S=6u,\ 10P=3u^2\). The reflected pair gives
\(5(2-S)=6w,\ 10(1-S+P)=3w^2\).
Solving (sum the two first equations, then subtract the two
second equations) gives
\[
             u=w=5/6,\quad v=1/6,\quad G=X^2-X+5/24 .
\]
There is another internal effective clock in each orientation.
At the first distinct nonzero new clock after \(u\), the
literal grade-four mask \(C(C-u)T\) vanishes on all predecessors,
even if the earlier clock \(u\) repeats. Its primitive error
through grade five is zero. For the fitted \(G\),
\[
       J[X(X-u)G](x)=x^2(x-u)^2(4x-3u)/20 .
\]
Therefore the second forward clock is \(5/8\), and reflection
gives \(3/8\) as the second clock from the right.
These are four different internals, exhausting the assumed
effective support. Its paid \(G\)-weighted quadrature forces
\[
 \int_0^1 X(1-X)(24X^2-24X+5)
              (6X-5)(8X-5)(8X-3)(6X-1)\,dX=0 ,
\]
although its exact value is \(233/210\).
This proves the assertion, including pure masks with zeros at some
extra literal clean rows.

## C. Exactly four distinct clean clocks are impossible

For four clean clock labels, anchored \(G\)-weighted
quadrature makes \(G\) times the two interior factors equal
\(L/42\), as in the
[fixed-four identity](ERK10-FOURTEEN-STAGE-EQUALITY.md).
Thus all four clean clocks are effective and distinct from
\(\alpha,\beta\), and all six live labels are the Lobatto
nodes. In particular the two r-labels have nonzero ordinary
pooled mass. The separate moments \(\sum b_i r_i^j=0\)
for \(j=1,2,3\) at each label imply that each needs at least
four distinct r-amplitudes: with at most three amplitudes
Vandermonde would force zero ordinary pooled mass.
There are at most five clean physical rows.

Equation (Z) yields \(\lambda_x=0\) at all four clean labels.
Thus all singleton clean rows have \(z=0\).
The first nonzero clean row and last clean row different
from 1 must have \(z\ne0\) by the verified fixed-four
first/reversed boundary primitive from the base packet.
There is at most one repeated clean label. Hence it is the
same internal clock \(u\) at both contacts, and the clean
chronology is \(0,u,v,u,1\). At the singleton middle \(v\)
all of \(F_5\) vanishes. The genuine grade-four clean mask
\(C(C-u)T\) is zero before \(v\); its grade-five
primitive there forces
\[
              J[X(X-u)G](v)=0 .                              \tag{C}
\]
For the four distinct Lobatto roots \(u,v,\alpha,\beta\),
Vieta gives \(180 J[X(X-u)G](v)=v^2 K(v)\), where
\(K=231X^3-390X^2+200X-30\).
The exact identity
\[
 (-32340X^2+35658X-8263)L+
   (5880X^3-8316X^2+3178X-280)K=137
\]
contradicts (C). This also handles any later case with this
same four-root arrangement and masked-clean chronology.

There cannot be fewer than four clean clock labels, by the
rank-four anchored argument in the base packet. With exactly
five or six clean physical sites all at distinct clocks,
the endpoint zeros of \(z\) leave at most four potential
nonzero \(\lambda_x\) in (Z), so all vanish and every
effective clean physical row has \(z=0\); §B excludes this.

## D. Six clean physical rows and five distinct labels are impossible

This is the remaining seven-active-tap case. The single repeated
clean label is \(u\); at least one endpoint is a singleton. Thus (Z)
first gives all \(\lambda_x=0\) on the five labels (having
one zero). By §B the repeated label must be effective with
some nonzero \(z\). By (E) it cannot be either endpoint.
The two other formal clean internal labels are singletons;
every effective one is a Lobatto root by §A.

If one singleton is masked out by \(G\), there are precisely
two effective clean internal labels. The potential ordinary
support then has at most six distinct clocks including
the endpoints, so it is exactly the six-point Lobatto rule.
Indeed one r-label shares the masked singleton clock, and
no further coincidence is possible with the six-node rule.
The two r-labels, \(u\), and the effective singleton are its
four distinct internals. A singleton cannot be the first or
last effective internal contact, by the fixed-four scalar
nonvanishing (the weighted support excludes the masked
singleton). Thus the effective chronology is \(0,u,v,u,1\)
with \(v\) the effective singleton. The contradiction (C)
applies unchanged.

Now both singleton internals \(v,w\) are effective.
If \(u\) is not a Lobatto root, (E) implies its ordinary
pooled clean weight is zero. The potential ordinary support
then lies in \(\{0,1,v,w,\alpha,\beta\}\), so canonical
Lobatto exactness forces \(\alpha,\beta\) to be the two
other Lobatto roots.
If \(u\) is a Lobatto root, the missing fourth root \(a\)
must equal one of the r-labels. To see this, extend the field to
contain \(a\) and compare the actual and canonical exact
quadratures on the single degree-seven polynomial
\[
       X(X-1)(X-u)(X-v)(X-w)(X-\alpha)(X-\beta).
\]
The actual value is zero; the canonical value is zero at
all but \(a\), and its weight at \(a\) is nonzero.
Therefore one of the last two factors vanishes there.

In either case there is a dirty Lobatto label \(a\), distinct
from the effective singleton labels. A singleton first or last
effective internal contact would be zero-pure through grade
five for the required linear polynomial primitives; §B's
one-sided two equations would require
\(10a^2-12a x+3x^2=0\) for distinct Lobatto roots \(a,x\)
(or their reflections). The exact prime-37 certificate below
excludes this. Hence the physical clean chronology, where
\(v,w\) are labelled in their actual order, is
\[
                        0,\ u,\ v,\ w,\ u,\ 1 .
\]
At the two singleton middle contacts the genuine polynomial
primitives give the pair of equations
\[
 f(u,v,\alpha,\beta)=f(1-u,1-w,1-\alpha,1-\beta)=0,\qquad
 f(u,v,a,b)=12v^3-15(u+a+b)v^2+20(ua+ub+ab)v-30uab .
\]
The first is (C) divided by the nonzero \(v^2/60\);
the second is its reflected analogue on the true principal
live reverse, with the primitive deviation paid in §A.
If \(u\) is a Lobatto root, these equations are both affine
in the free r-label \(\beta\), with \(u,v,w,\alpha\)
the four fixed roots after exchanging \(\alpha,\beta\) if
necessary. If \(u\) is not a Lobatto root the equations are
both affine in free \(u\), with \(v,w,\alpha,\beta\) the fixed
roots. For two affine functions \(F,G\), a shared root
forces \(F(0)G(1)-F(1)G(0)=0\); no leading-coefficient
assumption is hidden here.

The exact split-prime receipt:
- \(L\) has the four distinct residues \(6,8,30,32\) mod 37.
  The twelve ordered distinct-pair first-contact values are
  nonzero.
- The two determinant families above are nonzero for all
  24 permutations each of these residues.

This excludes the equations over every characteristic-zero field.
Indeed work in the finite rational splitting field of \(L\);
all its roots are integral over \(\mathbb Z_{(37)}\) since the
leading coefficient is a unit. The root algebra is integral,
so choose a maximal ideal above 37. The four roots stay distinct
after reduction, since the split polynomial is squarefree, and
their assignment to the chronological roles is one of the
checked permutations. Both the first-contact expressions and
the determinants are polynomials with integer coefficients in
these root parameters; a nonzero reduction proves exact
nonvanishing in characteristic zero. The free unknown is not
reduced and need not be integral. The argument for another
characteristic-zero field uses its finite subfield generated by
the same labelled algebraic roots. This closes the six-clean
physical case.

## E. Exact remaining six-tap scalar geometry

There were at least six active physical sites and at most nine.
Sections B–D exclude all cases with at most six clean physical
sites. Thus there are exactly six active and seven clean
physical live sites. By the marked Gram result the group sizes
are four and two, with a nonuniform four-row group.
The two-row group is an opposing uniform pair by its three
local moments, hence contributes zero ordinary pooled mass.
The four-row group has either four distinct amplitudes or two
opposing uniform pairs. In the latter case each of its two
same-amplitude pairs already differs in grade four and its
ordinary pooled mass is zero. In the four-distinct case its
ordinary pooled mass is nonzero (otherwise the four ordinary
Vandermonde moments at these amplitudes would all vanish).
In any case at most one dirty clock contributes to the pooled
ordinary measure.

Subtract the canonical six-point rule from the actual ordinary
read, cancel the individual endpoint weights \(b_1,b_{14}=1/30\),
and ignore the uniformly cancelling dirty pair.
The residual is supported on at most ten distinct sites:
five other clean physical sites, one possible pooled dirty clock,
and four internal canonical sites. This count still holds if
a clean endpoint repeats or dirty and clean clocks coincide.
Its first ten moment rows vanish. Vandermonde therefore makes
the residual zero and fixes the claimed pooled measure.

If all seven clean rows were at distinct clocks, there would be
five distinct singleton clean internals. With their nonzero
weights, pooled equality is possible only if the one nonzero
dirty mass cancels one of them at a coincident non-Lobatto
clock (the other four clean internals must be Lobatto).
That coincident clean clock is masked out by \(G\).
The two endpoint z-values are zero and at most four effective
internal clock rows remain in (Z), so all effective clean
z-values vanish. Section B excludes it. The remaining seven
clean rows therefore have five or six distinct clocks.
No claim of complete exclusion is made.

## F. An actual consecutive-row merge, not a reverse-order assertion

If physical rows 12 and 13 have the same clock \(x\), then in
the genuine live reverse \(A^\vee u\in W_2\) is proportional
to \(r\) on this clock. At row 13 it is zero by strictness,
and \(r_{13}\ne0\); it is therefore zero at row 12 as well.
Since the only other later row is the reversed origin with
\(u_{14}=0\), this forces \(A^\vee_{12,13}u_{13}=0\).
Thus \(A^\vee_{12,13}=0\). The clock sum now gives identical
literal reversed rows 12 and 13 (both read only row 14).
It follows that \(u_{12}=u_{13}\ne0\), hence \(r_{12}=r_{13}\ne0\).
As \(F_4|_I=W_3\subseteq\bar F_4\), the identical reversed
rows also make the two original evaluations agree on \(E_4\).
Moreover the original normalized outgoing columns satisfy
\(A_{\cdot,12}/b_{12}=A_{\cdot,13}/b_{13}\), including the
omitted ghost row by strictness.

If \(b_{12}+b_{13}\ne0\) this pair can be merged **literally**
in the forward tableau. Replace the two rows by their
\(b\)-weighted average, use weight \(b_{12}+b_{13}\), and
replace later taps to this pair by their sum. The earlier
rows are unchanged, each of the two original incoming
rows reads only earlier than physical 12, and the new
tableau stays strictly lower triangular. For any rooted
stage profile of grade at most nine, all its child factors
at the merged row are the corresponding affine averages.
A child factor that differs between the original rows has
grade at least five, because they agree through \(E_4\).
Two different such factors cannot occur simultaneously
at total grade at most nine. The product of the affine
averages is therefore exactly the affine average of the
products. Inducting on the rooted recursion, the
normalized outgoing-column equality preserves every
later rooted stage profile, and the combined output
preserves every order-ten rooted test. This would be a
strict 13-row order-ten tableau, impossible.
This merge needs neither real signs nor a full reversed
RK order theorem, but does need the nonzero combined weight.

In the surviving six-tap chart, the size-four group cannot
supply a same-clock row-12/row-13 pair. Four distinct
amplitudes preclude equal \(r\); and for two opposing
amplitude pairs, each equal-amplitude pair already splits
on \(E_4\) by (G) of the base packet. Thus if \(c_{12}=c_{13}\),
those two physical rows are exactly the uniformly
cancelling two-row group. The merge does not eliminate that
zero-sum possibility.

[ERK10SingleGhostClosureGate.lean](../lean/RKCert/Research/ERK10SingleGhostClosureGate.lean)
checks the exact Vieta, Bézout, affine and integral identities
and the full modular finite tests. The rooted, stage and
quadrature transfers above remain mathematical, using the
separately reviewed Hermite bound and base single-ghost packet.
