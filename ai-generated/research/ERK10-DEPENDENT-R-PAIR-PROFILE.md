# The constant-amplitude dependent ERK10 profile and two-pair exclusion

This continues the all-live case of the
[fourteen-stage order-ten equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
over a characteristic-zero field. All paid order conditions refer
to the **actual original** tableau or to its proven exact weighted
transpose. Assume \(d,Cd\) dependent. The shifted-nine tap floor
in both directions gives \(A_{21},A_{14,13}\ne0\).
Since \(d\) and \(d^\star\) span the same pure line and are
nonzero at rows 2 and 13, all quadratic defects are at
\(c_2=c_{13}=\theta\ne0,1\). We work here in the further fork
where these defects have **one common nonzero amplitude**.
Let \(s\) be their indicator and \(r=As\); the pure flag is
\[
   F_2=Ks,\quad F_3=\langle s,r\rangle,\quad
   F_4=\langle s,r,Cr\rangle .
\]
In fact \(r\notin Ks\): otherwise \(Ks\) would be an invariant
space for \(A,C\), and the paid triangular partial-inverse
argument applied to \(Ac-c^2/2\in Ks\) would give \(c\in Ks\).
The paid noninvariance argument at grade three gives the
third line. Call a stage a **carrier** if \(s_i=1\); call it
**active** if \(s_i=0,r_i\ne0\); the others are **clean**
in the stronger grade-four sense. Both endpoints are clean.

**Results.** If there are at least four carriers then the
active stages have at most **two distinct** numerical clocks.
If there are two, there are exactly four carriers and the
two active populations are \((2,2),(2,3)\) or \((3,3)\)
(up to exchange). Exactly six ordinary scalar support clocks
occur after pooling, and they are the fixed six Lobatto
clocks. The \((2,2)\) chart is impossible if **neither**
active clock equals \(\theta\). This leaves the same-clock
and triple charts, and does not claim a two-carrier exit or
a new unrestricted stage bound.

## Exact active population count

The carrier moments \(b(s r^j)=0\) for \(j=0,1,2\)
cost grades \(2,5,8\). Thus carrier sums contribute zero
to each active moment below because \(c=\theta\) there.
On the active positions the signed masses \(b_i r_i\)
have zero scalar moments through six, and \(b_i r_i^2\)
through three. These are the pure tests \(r\in F_3\),
\(r^2\in F_6\), with clock multiplication.

Assume at least four carriers, so there are at most eight
active rows (two physical endpoints are clean).
If the pooled \(b_i r_i\) measure is nonzero, it has at least
eight active clock labels by Vandermonde. There must be
exactly eight active rows at distinct clocks, four carriers,
and just the two endpoints otherwise. Write \(D_8\) for
the monic hull of those eight clocks. The one-dimensional
moment kernel gives \(b_i r_i=\kappa/D_8'(c_i)\).
Let \(R\) be the interpolant of the eight values \(r_i\).
If \(4\le\deg R\le7\), test \(b_i r_i^2 c_i^j\)
with \(j=7-\deg R\). It returns \(\kappa\) times the
nonzero leading coefficient of \(R\) by Lagrange's
degree-seven coefficient formula, contradiction.
Thus \(\deg R\le3\). For every \(Q\) of degree at most
three the weighted sum of \(X(1-X)R(X)Q(X)\) on all rows
vanishes: on active rows substitute \(r_i=R(c_i)\)
and use its paid pure moments; the carrier \(b\)-sum
is zero and the endpoint factors handle the last two
rows. Ordinary exactness then makes \(R\) orthogonal to
all degree-three polynomials for \(X(1-X)\). The paid
Beta determinant forces \(R=0\), impossible.

Consequently the pooled \(b_i r_i\) measure is zero.
Each active label requires at least two rows, so there
are at most four labels. Vandermonde makes the second
pooled measure \(b_i r_i^2\) zero at every label as well.
If an active group has exactly two rows,
the two equations, with both \(r_i\) and \(b_i\) nonzero,
force the \(r\)-values equal and the two weights opposite.
In particular it contributes zero ordinary scalar mass.
With \(k\ge4\) carriers and \(q\) active labels, the number
of effective ordinary scalar clock labels is at most
\[
  \#\{\text{clean rows}\}+\#\{\text{active groups of size at least 3}\}
                  \ \le\ 14-k-2q .
\]
There must be at least six labels: more precisely, there
must be at least six distinct labels across the whole clean
list plus active groups with nonzero pooled ordinary mass,
since that list includes the endpoints and supports a
degree-nine ordinary quadrature. Otherwise the paid
\((1-X)\)-Gram test of the equality ledger applies.
Thus \(q\le2\). If \(q=2\), equality throughout gives
\(k=4\), active group sizes at most three, and exactly six
distinct scalar support sites including 0 and 1. Each active
triple contributes a nonzero scalar mass. The six support
sites are exactly the standard six Lobatto sites by the
same uniquely paid Jacobi polynomial.

## The 2+2 chart with distinct active clocks from the carrier

Write the active clock labels as \(\alpha,\beta\) and
assume \(\alpha,\beta,\theta\) pairwise distinct.
Each active group is now a uniform \(r\)-value opposite-weight
pair. Since \(b r^3=0\) is paid at grade nine, and both
active pairs cancel separately, \(b(s r^3)=0\) holds also.
The four carrier \(r\)-moments through degree three force
any group of equal carrier \(r\)-value to have zero mass.
If all four carrier \(r\)-values agree they are zero (from
row 2), and then \(F_4\) is the direct sum of the carrier
indicator and the two active pair indicators. It is
C-invariant and closed under coordinatewise products, so
the [reviewed rank-three core obstruction](../lean/ERK-GRADE-EIGHT-OFF-CORE.md)
forbids it already at order ten. Otherwise there are
exactly two opposite-weight carrier pairs with nonzero
difference. Their values are \(0,a\ne0\).

There are now four tagged pairs, and every \(E_4\) vector
is constant on each pair. If \(x_0,x_1,x_2,x_3\) denote
the signed weighted pair differences of an \(E_5\) vector
at, respectively, carrier \(r=0\), carrier \(r=a\),
active \(\alpha\) and active \(\beta\), then \(E_5=F_4^{\perp_B}\)
gives
\[
 x_0+x_1=0,\quad a x_1+r_\alpha x_2+r_\beta x_3=0,\quad
 \theta a x_1+\alpha r_\alpha x_2+\beta r_\beta x_3=0.
\]
This line has every coordinate nonzero on a nonzero vector:
after \(x_0\) is eliminated, the last two equations are the
two Vandermonde tests on three distinct clocks with
nonzero rescalings. It occurs in \(E_5\), since the space
of vectors constant on all four pairs has dimension ten
and \(E_5\) has dimension eleven. Thus **every** tagged
pair genuinely splits in grade five.

The six clean sites are precisely the six Lobatto sites.
Put \(G(X)=(X-\alpha)(X-\beta)\); the actual grade-two
vector
\[
                   T=G(c)-G(\theta)s
\]
is zero on all four tagged pairs, and has value \(G(c)\)
on clean rows. Its model is \(G\).
The same literal first and last clean read of \(C T\)
and \((1-C)T\) as in the balanced independent chart
pays the two primitive identities
\(\int_0^u XG(X)=\int_v^1(1-X)G(X)=0\).
The endpoint test with \(T\) if \(G(0)=0\), and its reflection,
prove \(G(0)G(1)\ne0\) just as before.
Thus the [checked clean noncontacts](ERK10-BALANCED-SEVEN-SEVEN.md)
apply: \(G\) is nonzero at all six clean clocks.

## Transfer of the literal 7|7 and seam matrix

We give the profile replacements needed to reuse the
[balanced half argument](ERK10-BALANCED-SEVEN-SEVEN.md),
rather than only matching the number of rows.

* A vector in \(E_3\) can realize arbitrary values on
  the four dirty tags: first use \(r\) to fix the difference
  between the two carrier tags at their common clock, then
  a quadratic in \(c\) to fit the three numerical clocks.
  By adding \(T L_1(c)\) it can also fit any two clean tags,
  since \(G\) is nonzero at all clean tags.
  Consequently no pair repeats before the third clean row,
  or, by reflection, after the fourth clean row. Thus
  each physical half contains four dirty and three clean rows.
* In the only plausible intra-half duplicate chronology,
  there must be three distinct dirty tags at rows 2–4,
  clean rows at 1,5,6, and the repeated dirty tag at row 7:
  the first nonzero clean \(u\) requires order four on its
  true predecessors. If \(E_3\) is full on the first six
  states, the pair cannot differ in grade five. If its
  rank is five there, take any nonzero grade-three vector
  vanishing on the first five (its restriction there is
  full). It cannot be pure: \(s,r\) restrict independently
  on any three of the four dirty tags, as those three
  always include a carrier and a nonzero active tag.
  Hence its model is nonzero. The rank-five assumption
  gives its zero at the sixth stage, so its model is a
  nonzero multiple of \(X(X-u)(X-w)\).
  The point-exact unary tests at \(u,w\) give the
  contradictory \(2w=u,\ 2u=w\).
  Thus all four pairs cross the physical 7|7 cut.
* Adding \(T L_2(c)\) after fitting the dirty four shows
  that \(E_4\) surjects onto either half. Its half-zero
  lines \(V_L,V_R\) are supported on the opposite **clean**
  sites because all dirty tags occur in both halves.
  The pure vectors \(s,r,Cr,C^2r\) at grade five fit
  all four dirty tag values independently: isolate the
  \(r\)-values at the three distinct clocks, then use \(s\).
  Thus any \(E_5\) vector supported on clean rows has its
  model given by ordinary degree-five interpolation on
  those six sites, in either orientation, after correcting
  the dirty values by those pure vectors. No equality of
  the whole grade-five pure flags is needed.
* The actual \(A V_L\) is zero on the left. If one
  right dirty coordinate were zero, the single pair-difference
  line makes all four zero, so \(A V_L\) would be clean-only.
  Its interpolated model \(J P_L\) would have both value
  and derivative zero on the three left clean clocks,
  impossible for a nonzero polynomial of degree at most
  five. Thus all four right dirty sites have nonzero unary
  values, and row 8 is clean because a strict unary read of
  \(V_L\) is zero there. Reflection forces row 7 clean.

Finally write a half-zero model and vector as
\[
               V=P(c)+f s+r\,q_1(c),\qquad \deg q_1\le1 .
\]
Both carrier tags are zero for \(V\): the \(r=0\) tag
gives \(f=-P(\theta)\), and the \(r=a\) tag then gives
\(q_1(\theta)=0\). Therefore \(q_1(X)=e(X-\theta)\).
At the active tags
\[
                    P(\xi)=-e\,r_\xi(\xi-\theta),
                                      \qquad \xi=\alpha,\beta.
\]
Here \(e\ne0\), since otherwise \(P\) would vanish at the
two active clocks and its own three clean clocks, five
different values despite degree at most four.
Scaling either half alias by a nonzero factor now makes
their two models have one shared **nonzero** remainder
modulo \(G\). The exact two
[paid linear seam products and their 24-case determinant](ERK10-BALANCED-SEAM-EXCLUSION.md)
apply unchanged, with the present clean-only vector \(T\).
The same matrix depends only on the six clean Lobatto
nodes and normalized \(G\), not the physical dirty hull.
Its nonzero determinant forbids the shared residue.
This closes exactly the stated two-pair chart.

[ERK10DependentPairGate.lean](../lean/RKCert/Research/ERK10DependentPairGate.lean)
checks the two-moment pair cancellation and all-nonzero
difference-line gate. The contact and determinant arithmetic
is reused from its existing Lean files; the native tableau
bridges are mathematical. In the remaining same-clock
case one of the two active labels equals \(\theta\);
the two difference tests instead force the other active
pair equal in \(E_5\), so the four-pair transfer above does
not apply. The triple populations are separate.
