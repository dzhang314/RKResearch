# The zero-mass triple has exactly one cross-front pair

**Scope.** Continue the maximal all-live two-total-carrier,
both-new-boundaries ERK11 chart. Assume the first pooled
response vanishes at all six distinct active noncarrier labels,
and there are **thirteen** active rows, hence five pairs and
one triple. The weighted response decomposition below is
characteristic zero. If the ordinary scalar pool of the triple
vanishes, the exact finite certificate over ordered fields forces
**exactly one** pair to meet both fronts. The one-cross topology
and the nonzero-mass triple are not excluded here. No numerical
stage bound changes.

ERK11SixTripleCrossGate.lean checks local moment arithmetic,
exact parameter enclosures, the exceptional endpoint residue,
and 192 interval differences. The rooting and chronology
bridges are the mathematical proofs below.

## 1. The triple's scalar block, including its degeneracy

Use the physical response scale \(F=\theta r\) and write
\[
  \nu_x=\sum_{c_i=x}b_iF_i=0,\qquad
  \mu_x=\sum_{c_i=x}b_iF_i^2,\qquad
  \tau_x=\sum_{c_i=x}b_iF_i^3 .
\]
All sums refer to active sites only. The five actually paid
square moments give \(\mu_x=k/D'_6(x)\) with
\(D_6=\prod_{\text{active }x}(X-x)\).
If \(k=0\), then all pairs have equal responses and opposite
ordinary weights. Their scalar mass vanishes, so ordinary
scalar moments would be supported on at most the triple's
clock and the two endpoints, impossible. Thus all six
\(\mu_x\ne0\). Each pair has distinct responses \(u,v\)
and nonzero ordinary mass \(B_x=-\mu_x/(uv)\).
Both clean fifth rows 5 and 13 are active: only the two
endpoint noncarriers are dormant.

At each active label project off its response line \(F\):
the projection coefficient is \(\langle z,F\rangle_x/\mu_x\).
The simultaneous numerical response space is six-dimensional
and nondegenerate under the actual weight form. On a pair this
leaves its constant scalar slot. On the triple it leaves a
nondegenerate two-dimensional space with constant direction \(1\).
If the triple ordinary mass \(B_p\ne0\), this splits as the
constant line of weight \(B_p\) and its nondegenerate orthogonal
shape line. If \(B_p=0\), the constant is isotropic and the
two-space is hyperbolic. In particular there is no division
by \(B_p\) in that case.

With the two dormant endpoint slots, this scalar space is
nine-dimensional in either case. The response projection
coefficients of a numerical \(E_j\) vector have degree
at most \(j-3\), \(3\le j\le7\), exactly as in the
[six-pair slope calculation](ERK11-SIX-PAIR-SITE-MASK.md):
test the actual products of grades \(j+3+i\le10\) and use
the barycentric \(\mu_x\) weights. At the triple this refers
to the projection coefficient, not a claim that the three
physical values are affine in \(F_i\). The actual ambient
\(E_6\) is the scalar nine-space, the response slopes of
degree at most three, and the carrier line \(\langle s\rangle\),
by \(E_6=F_4^{\perp_B}\) and its measured rank fourteen.

The two paid cubic moments give \(U_3\) of degree at most
three with \(\tau_x/\mu_x=U_3(x)\). Consequently
\(S=F^2-U_3(C)F\) is an actual pure grade-six vector in the
scalar space. At a pair \(S=-uv\); at the triple its mean is
\(\mu_p\). When \(B_p=0\), all three triple responses are
distinct (otherwise the two pooled equations \(B_p=\nu_p=0\)
would already force \(\mu_p=0\)). The cubic hull of their
responses gives
\[
 U_3(p)=u+v+w,\qquad
 \langle S,S\rangle_p=-(uv+uw+vw)\mu_p .
\]
The scalar triple block is then explicitly spanned by \(1,S_p\)
with mixed read \(\langle1,S_p\rangle=\mu_p\ne0\).
These are local, numerical fourth-response identities, not
additional paid order conditions.

## 2. Scalar-zero case and the exact omitted-clock possibilities

Assume now \(B_p=0\). The only scalar support sites
are the five active pair clocks and 0,1. They are all distinct:
a collision would leave at most six possible sites including
0 and 1, whose degree-six anchored hull contradicts the
paid weight-\(X(1-X)\) Gram. Every one has nonzero ordinary
pooled weight; the endpoints are individually live and
the triple contributes zero. Thus the pair clocks, in
particular, are not 0 or 1. Their monic hull \(H_5\)
is the earlier \(R_5+\lambda R_4\) Jacobi pencil up to scale,
by the ordinary degree-ten quadrature. Here
\[
 R_4=42X^4-84X^3+56X^2-14X+1,\qquad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1 .
\]
The polynomials are coprime by the
[previous integer identity](ERK11-ARBITRARY-PREFIX-JACOBI-GATES.md#3-the-full-tableau-polynomial-ambiguity-at-every-grade-610);
thus \(R_4\) is nonzero at each root of the pencil (also
reflected) for every parameter. No case with \(R_4=0\)
is lost by taking the parameter ratios below.

Let \(a\) be the left plateau, \(d=1-b\) the right plateau,
and \(e=1-b/2=(1+d)/2\) the right half-plateau. The two left
calibration clocks are \(a,a/2\), right \(d,e\).
Each front has four active clocks, and each plateau
appears twice at that front. These plateau clocks are distinct
from each other, since a group of four active sites is impossible.
If \(p\) is none of these four labels, both doubling tests
of the [earlier Jacobi obstruction](ERK11-TWO-CARRIER-JACOBI-POOL-EXIT.md)
hold and contradict \(V(\lambda)\) coprime to \(V(-\lambda)\).
Therefore \(p\) is one or two calibration labels, at most
one on either front.

The triple label is not an endpoint. For example if \(p=0\)
it is not a left calibration clock since the left \(a\ne0\).
Then both left calibrations lie among the five pair clocks.
The right omitted clock must be \(d=0\) or \(e=0\).
In the first case \(e=1/2\) is a pair clock, forcing
\(\lambda=0\) since \(R_5(1/2)=0,\ R_4(1/2)=1/8\).
But \(V(0)=31138569\ne0\).
In the second case \(b=2,d=-1\), so
\(\lambda=R_5(2)/R_4(2)=903/197\). The required
cleared numerator \(197^8 V(903/197)\) is \(4\bmod13\),
hence nonzero. Reflection gives the same exclusions at \(p=1\).

The other finite clock families are exhaustive up to reflection.

* If only a left calibration is omitted, both \(d,e\) are
  pair clocks. Then \(b\) is a root of the earlier nonzero
  doubling polynomial of degree eight. It has four real
  roots. The hull polynomial without division is
  \(R_4(b)R_5(X)+R_5(b)R_4(X)\), with known roots \(d,e\)
  and three further roots. If \(p=a/2\), the left plateau
  \(a\) is one of those three further roots: \(a=e\) would
  put the right half stage into the complete pair already
  occupied by the two left plateau stages. This gives 12
  clock charts. If \(p=a\), the left half \(a/2\) can be any
  pair clock other than \(d\), which is already a complete
  right plateau pair. This gives 16 charts.
* If \(p=a/2=e\), then \(a+b=2,\ d=a-1\).
  The roots \(a,d\) of \(H_5\) impose the earlier one-apart
  polynomial \(2772u^8-3528u^6+1212u^4-104u^2+1=0\)
  on \(u=a-1\). Its eight real roots give eight charts.
* If \(p=a=e\), put \(x=a/2\). The roots \(x,d=4x-1\)
  of the hull give
  \[
  \begin{split}
  R_5(x)R_4(4x-1)-R_5(4x-1)R_4(x)
     &=-2(3x-1)M_8(x),\\
  M_8(x)&=709632x^8-2483712x^7+3677184x^6-3010896x^5\\
       &\quad+1491162x^4-456720x^3+84184x^2-8480x+353 .
  \end{split}
  \]
  The factor \(3x-1=0\) would make \(x=d\), putting the
  left half-stage into the complete right plateau pair,
  impossible. Six real roots of \(M_8\) give six charts,
  with \(p=2x,d=4x-1\), and hull
  \(R_4(x)R_5(X)-R_5(x)R_4(X)\).
  The case \(p=a/2=d\) is its reflection.
  There are no other ways for one omitted label to affect both
  fronts, because the two plateau clocks themselves differ.

The orientation flip here refers to polynomial variables and the
clock schedule, not to assuming ordinary reverse order eleven.
These 42 charts prescribe the possible clocks but do not fix
all physical occurrences.

## 3. Exact cross-pair obstruction and literal one-cross chronology

A **cross-front pair** is an active pair label occurring in
both calibrated fronts (first seven and last seven, respectively).
It cannot be a plateau pair because that pair is entirely on
one front; the unique triple is not a pair.
Let \(F_L(x)=x^2(a-x)/a,\ G_R(x)=(1-x)^2(x-d)/b\) be
the actual left and right response profiles at off-plateau
calibration clocks. The right physical response scale is
\(G=\kappa F\), with \(\kappa\ne0\). At every cross-front
pair the two responses in scale \(F\) are
\(F_L(x)\) and \(G_R(x)/\kappa\).
Since \(\mu_x=-B_x u_x v_x=k/D'_6(x)\), it follows that
\[
                         k\kappa=-B_x D_6'(x) F_L(x)G_R(x).
\]
All factors used are live by the distinct active pair clocks
and their nonzero responses.

Write \(D_7=X(X-1)H_5\) and \(D_6=(X-p)H_5\). At an
interior root \(x\) the ordinary scalar weight has
\(B_xD_7'(x)=\int D_7(X)/(X-x)\,dX\).
As in the prior Jacobi mask argument this integral times
\(R_4(x)\) is one nonzero constant independent of the root:
move \(R_4(x)\) to \(R_4(X)\) using the orthogonality of
\(H_5\) against cubics, then pair its quotient's leading
coefficient with the \(R_4\) norm. Thus at every cross-front
pair, up to one common nonzero factor,
\[
          k\kappa\ \propto\
             \frac{N(x)}{R_4(x)},\qquad
          N(X)=(X-p)X(1-X)(a-X)(X-d).
\]
Any two distinct cross-front pairs must give the same value.

The exact interval checker refutes every such equality by
testing \(N(x)R_4(y)-N(y)R_4(x)\), before any ratio.
It encloses all real roots of the parameter polynomials:
four sign boxes for the degree-eight doubling polynomial
(Sturm variations 6 and 2), eight for the one-apart
polynomial (degree eight and eight sign changes), six for
\(M_8\) (Sturm variations 7 and 1). For each parameter box,
two hull roots are supplied by the chart and the other three
have checked disjoint uniform sign changes at rational
endpoints. The repeated-root boundary and \(R_4\) zeros are
excluded by these isolators and the exact coprimality argument.
Thus the charts cover all real-clock assignments, not just
samples of parameters.

In the one-left-half and both-half families compare all
pairs among the **three** hull roots off both plateaus,
whether or not the physical chronology uses them as crossing
sites. In the one-left-plateau and mixed families compare
all pairs among the **four** hull roots off the remaining
plateau. The totals \(12\cdot3+16\cdot6+8\cdot3+6\cdot6=192\)
are all strictly separated. The integer interval arithmetic
uses a \(10^{-36}\) grid with outward rounding, and the
ordered-field completeness follows in a real closure.
No actual root product is paid by the interval routine.

At least one cross-front pair is necessary.
If neither plateau is the triple, each is entirely on its own
front, and each front draws three other labels from four,
so the overlap has at least two labels before excluding \(p\).
If one plateau is the triple, the opposite complete plateau
is still confined to its front. Outside these two clocks
the first front draws three labels out of four, and the other
draws at least two, again forcing a shared pair.
The exact comparisons exclude two or more cross pairs, so
exactly one survives. The literal middle chronology is then:

* If neither plateau is the triple, the triple label must
  occur at both fronts, along with the unique cross pair.
  Each front has one other, exclusive label. The three inner
  middle stages (8,9,10) are respectively the third triple
  occurrence and the two missing partners, in some order.
* If a plateau is the triple, the opposite front must contain
  its third occurrence; otherwise at least two pairs cross.
  The three inner middle stages are the missing partners
  of the three exclusive pair labels, in some order.
  No middle stage is then the triple.

This is an exact remaining topology, not a claim of a
real tableau satisfying it.

The [Lean interval and scalar receipts](../lean/RKCert/Research/ERK11SixTripleCrossGate.lean) were independently replayed on Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1. The ordered-field and physical chronology implications are the source proof above.
