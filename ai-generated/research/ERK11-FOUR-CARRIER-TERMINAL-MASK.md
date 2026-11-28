# Exclusion of the ordered four-carrier ERK11 chart

**Scope.** This excludes the conditional 17-row chart in
[the four-carrier reduction](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
over ordered fields, in particular over the reals. It assumes all
ordinary weights are nonzero, the maximal rank-two half-clock tail
has both late quadratic carriers, and takes the actual two-ended
tableau and order-eleven reversal established there. The quadratic
carriers are exactly physical \(2,5,13,16\), all at one clock
\(\theta\ne0,1\). The branch with just one late carrier, the nonhalf
and nonmaximal/nonendpoint branches, and cases with a zero ordinary
weight are not excluded here. No ordinary minimum-stage bound changes.

No individual weight is assumed positive. Ordering is used in the
known first/second-middle clock guards; the terminal elimination
from those clock and support premises is characteristic-zero algebra.
The companion ERK11TerminalMaskGate.lean checks the indicated scalar
identities and certificate. Full rooted, grade, pooled-support and
mask transfers below are mathematical deductions from the earlier
tableau results, not new native stage theorems.

## 1. The exact paid pooled moments

Write \(s\) for the carrier indicator, \(r=As\), and \(c=A\mathbf1\).
Thus \(s,r\) are actual pure grades two and three; see
[the actual middle gate](ERK11-FOUR-CARRIER-MIDDLE-GATES.md).
On noncarriers the reverse response is \(\bar r=\lambda r\) with
\(\lambda\ne0\), in clock \(1-c\). The endpoint responses are
zero, from the two grade-five exact endpoints. The six calibration
noncarrier rows \(3,4,6,12,14,15\) are response-active, meaning
\(r_i\ne0\). Clock \(\theta\) repeats at 4 and 14. Furthermore
rows 7 and 11 are active and their clocks are new relative to their
respective fronts, by the ordered boundary gate. The
[second-middle neighbours](ERK11-FOUR-CARRIER-NEIGHBOUR-PENCIL.md#1-genuine-first-and-second-middle-functionals)
give activity at rows 8 and 10, and relative to each front their
clock avoids all three calibration clocks, the origin and the
preceding middle clock. Only center 9 can additionally be active;
only it may add another active site at \(\theta\).
Thus the noncarrier active site count \(n\) is 10 or 11, and there
are at least five distinct active labels (already left 3,4,6,7,8).

At each active clock \(x\) form the three signed pools over
the active noncarriers there:
\[
 \nu_x=\sum b_i r_i,\qquad
 \mu_x=\sum b_i r_i^2,\qquad
 \tau_x=\sum b_i r_i^3 .
\]
Let \(M_3=\sum_{i\text{ carrier}} b_i r_i^3\).
The three carrier-local products \(b(s r^j)=0\), \(0\le j\le2\),
pay grades \(2+3j=2,5,8\), with zero models.
Thus carrier contributions to \(b(C^k r)\) and \(b(C^k r^2)\)
vanish for any \(k\). The actual noncarrier active moments are
\[
  \sum_x x^k\nu_x=0\quad (0\le k\le7),\qquad
  \sum_x x^k\mu_x=0\quad (0\le k\le4),\qquad
  \sum_x\tau_x=-M_3,\quad \sum_x x\tau_x=-\theta M_3.          \tag{1}
\]
Costs are respectively \(3+k,6+k,9+k\le10\), since
order eleven pays grade at most ten. No carrier product
\(b(s r^3)\) is assumed: its grade would be eleven.
The last two equations allow \(M_3\ne0\).

Write \(q\) for the distinct active noncarrier clock count.
If \(\nu=0\), every active label has multiplicity at least
two since all \(b_i\) and the selected \(r_i\) are nonzero.
Thus \(q=5\) and \(n=10\) or 11. The five square moments then
give \(\mu=0\) by Vandermonde. At a double label these two
equalities force the two nonzero responses equal and weights
opposite, so its ordinary scalar mass is zero. The alternatives
are all five pairs, or one triple and four pairs. The scalar
mass of the four carriers at \(\theta\) is zero by \(b(s)=0\).
Counting endpoints and the optional inactive center or one
triple, the ordinary scalar quadrature would have at most
three nonzero pooled sites. The square of their nonzero
hull, of degree at most six, contradicts ordinary moments
through degree ten (nonsingular ordinary positive Gram).
Thus \(\nu\ne0\). Eight moments force \(q\ge9\), and the
repeat \(\theta\) forces \(q\le n-1\le10\).

## 2. A literal cubic profile off the repeated carrier clock

For the \(q\) active labels put \(D(X)=\prod_x(X-x)\).
Lagrange interpolation gives
\(\sum_x U(x)/D'(x)=0\) for \(\deg U\le q-2\). A pool vector
orthogonal to clock powers through degree \(k\) is uniquely
\(U(x)/D'(x)\) for \(\deg U\le q-k-2\): those numerators
inject under evaluation and give the full nullity \(q-k-1\).

**Nine labels.** Then \(\nu_x=\kappa/D'(x)\), \(\kappa\ne0\),
and \(\mu_x=\nu_xR(x)\) for a polynomial \(R\) of degree
at most three. At every singleton \(r_i=R(c_i)\). Put
\(\Delta_x=\tau_x-\nu_xR(x)^2\). The baseline
\(\nu_xR(x)^2\) sums to zero against 1 and \(X\) by the
degree-seven \(\nu\)-moments. Thus the discrepancy has sum
\(-M_3\) and first moment \(-\theta M_3\). There is at most
one off-\(\theta\) repeat, which would be a pair. Subtracting
\(\theta\) times the zeroth moment from the first gives
\(\Delta_x=0\) at that pair. Its two sites satisfy
\[
       \nu_x\tau_x-\mu_x^2
       =(b_i r_i)(b_j r_j)(r_i-r_j)^2,                        \tag{2}
\]
so \(r_i=r_j=R(x)\), because amplitudes, weights and
\(\nu_x\) are nonzero. The cubic is literal at every
off-\(\theta\) active noncarrier.

**Ten labels.** Now \(n=11\), \(\theta\) is the sole double
and all others singletons. Write \(\nu_x=P(x)/D'(x)\)
and \(\mu_x=M(x)/D'(x)\) for \(\deg P\le1,\deg M\le4\).
The polynomial \(P\) is nonzero and cannot vanish at any
singleton. Their literal response is \(M(x)/P(x)\).

* If \(P\) is constant, subtract \(M(x)^2/(P D'(x))\) from
  \(\tau_x\). The discrepancy is supported at \(\theta\);
  its zeroth moment is \(-M_3\) because \(\deg M^2\le8=q-2\).
  The first moment of the base alone is accordingly zero.
  Its degree-nine leading coefficient is the square of the
  degree-four coefficient of \(M\), divided by \(P\);
  Lagrange interpolation makes this coefficient the first
  moment. Hence \(\deg M\le3\).
* If \(P\) is linear with root \(\xi\ne\theta\), then
  \(\xi\) is off all active labels. Write
  \(M^2/P=Q+\gamma/(X-\xi)\), \(\deg Q\le7\).
  Subtract the baseline \(M(x)^2/(P(x)D'(x))\) as above.
  The polynomial parts of both moments vanish. Subtract
  \(\theta\) times the zeroth compensated moment from the
  first to give \(\gamma(\xi-\theta)S=0\), where
  \(S=\sum_x1/((x-\xi)D'(x))=-1/D(\xi)\ne0\).
  Here the extra term from multiplying \(1/(x-\xi)\) by
  \(x\) vanishes by the constant barycentric identity.
  Thus \(\gamma=0\), \(M(\xi)=0\), and \(R=M/P\) is cubic or lower.
* If \(P=k(X-\theta)\), subtract \(\theta\) times the zeroth
  moment directly from the first in (1). The repeat and
  carrier contributions disappear. After multiplication
  by \(k\ne0\), the singleton contributions give
  \(\sum_{x\ne\theta}M(x)^2/D'(x)=0\). The full barycentric
  sum vanishes by degree at most eight, so \(M(\theta)=0\).
  Again \(R=M/P\) is a cubic or lower on every singleton.

In both possible label counts a literal cubic \(R\) exists
at every active noncarrier with \(c_i\ne\theta\). A left
calibration site is off \(\theta\) and has nonzero response,
so \(R\) is nonzero.

## 3. Localize an actual grade-four vector to the endpoints and center

Set \(G(X)=(X-\theta)R(X)\). The actual grade-four vector
\[
               T=(C-\theta I)(R(c)-r)
\]
has model \(G\). It vanishes on all carriers and all sites
of clock \(\theta\), and at every active noncarrier with
other clock by the literal cubic. Its only possible support
is rows 1, 17 and the dormant center 9 (if \(r_9=0\)).
Test it against \(C(1-C)S(c)\), \(\deg S\le4\), costing
at most \(4+6=10\). If just the endpoints contribute, then
\(\int X(1-X)G(X)S(X)\,dX=0\) for all such \(S\),
contradicting the nonsingular weighted Gram and \(G\ne0\).
In particular \(n=11\) is impossible, and \(n=10,q=9,r_9=0\).
Write \(w=c_9\). The same argument requires \(w\ne0,1,\theta\)
and \(G(w)\ne0\).

If the carrier responses are the two opposing pairs of the
earlier chart, then \(M_3=0\), and the now-sole \(\theta\)-pair
has zero discrepancy, so (2) gives the literal cubic there too.
This is already excluded by the
[older two-front cubic calculation](ERK11-FOUR-CARRIER-MIDDLE-GATES.md#a-stronger-cubic-exclusion-and-literal-path-test-when-both-sides-are-new).
The following handles both carrier patterns, including \(M_3\ne0\).

The same paid tests now read only row 9:
\[
   \int_0^1 X(1-X)G(X)S(X)\,dX
         =b_9w(1-w)G(w)S(w)\quad(\deg S\le4).                 \tag{3}
\]
Write \(V(X)=(1,X,X^2,X^3,X^4)^{\mathsf T}\), and
\[
 N=\begin{pmatrix}
3&-32&108&-144&66\\
-32&388&-1404&1956&-924\\
108&-1404&5316&-7644&3696\\
-144&1956&-7644&11256&-5544\\
66&-924&3696&-5544&2772
\end{pmatrix},\qquad K(X,Y)=V(X)^{\mathsf T}N V(Y).
\]
The Gram with entries \(1/((i+j+2)(i+j+3))\),
\(0\le i,j\le4\), has inverse \(210N\) (Lean checks
the integer clearing with denominator 27720).
Equation (3) gives \(G(X)=k K(X,w)\) for some \(k\ne0\).
In particular \(F_0(\theta,w)=K(\theta,w)=0\).
Thus \(R\) is a nonzero scalar times the polynomial
\[
              Q_{\theta,w}(X)
                  =\frac{K(X,w)-K(\theta,w)}{X-\theta}.
\]
If \(K(X,w)=\sum_{i=0}^4 k_i(w)X^i\), the coefficients
of this quotient are
\(k_4,k_3+\theta k_4,k_2+\theta k_3+\theta^2k_4,
 k_1+\theta k_2+\theta^2 k_3+\theta^3k_4\) in descending order.

## 4. Both fronts impose homogeneous conditions on the same cubic

Let \(R(X)=a+bX+dX^2+eX^3\). Its normalized polynomial
\(R(\theta X)/\theta\) agrees with \(F=X^2(1-X)\) at
\(1/2,z,x\), where \(z=c_6/\theta,\ x=c_7/\theta\).
These labels are pairwise distinct and all three actual
sites are active off \(\theta\). The paid first-middle
gate gives \(6zx-7(z+x)+8=0\). The difference
\(U=R(\theta X)/\theta-F\) is zero or a constant times
\((X-1/2)(X-z)(X-x)\). Its coefficients satisfy
\(6U_1+10U_2+13U_3=0\): for the quotient by \(X-1/2\),
six times the constant, seven times the linear and eight
times the quadratic coefficient vanish in sum. Thus
\[
         6b+10\theta d+13\theta^2 e=-3,\qquad
                       R(\theta/2)=\theta/8 ,
\]
which give the homogeneous condition
\[
   \theta(6b+10\theta d+13\theta^2 e)+24R(\theta/2)=0.         \tag{4}
\]
In the opposite model the response at active noncarriers
is \(\lambda R(1-(1-\theta)X)/(1-\theta)\).
The reflected first three actual distinct labels give
exactly the same normalized read and clock gate. So (4)
holds for \(R(1-X)\) at \(1-\theta\), since \(\lambda\ne0\)
cancels in the homogeneous test. No equality between
\(\lambda\) and \((1-\theta)/\theta\) is assumed.

Substitute \(Q_{\theta,w}\) for \(R\) in these homogeneous tests.
The two polynomials are
\[
 \begin{aligned}
 F_L(U,W)&=24k_1(W)+42U k_2(W)+58U^2 k_3(W)+74U^3 k_4(W),\\
 F_R(U,W)&=-F_L(1-U,1-W).
 \end{aligned}                                                \tag{5}
\]
Indeed \(K(1-X,1-Y)=K(X,Y)\) by symmetry of the weight
and uniqueness of the reproducing kernel, so the reflected
quotient is \(-Q_{1-\theta,1-w}(X)\). In particular
\(F_0(\theta,w)=F_L(\theta,w)=F_R(\theta,w)=0\).

## 5. Degree-preserving modular certificate, without missed fibers

View \(F_0,F_L,F_R\) as quartics in \(W\) with integer
polynomial coefficients in \(U\). For \(a=(a_0,\ldots,a_4)\)
the coefficients of \(F_0\) and \(b=(b_0,\ldots,b_4)\)
those of \(F_L\) or \(F_R\), put \(d_{ij}=a_i b_j-a_j b_i\).
The Bezout determinant is the determinant of
\[
 \begin{pmatrix}
 d_{10}&d_{20}&d_{30}&d_{40}\\
 d_{20}&d_{30}+d_{21}&d_{40}+d_{31}&d_{41}\\
 d_{30}&d_{40}+d_{31}&d_{41}+d_{32}&d_{42}\\
 d_{40}&d_{41}&d_{42}&d_{43}
 \end{pmatrix}.
\]
This matrix gives the coefficients of
\((a(X)b(Y)-b(X)a(Y))/(X-Y)\).
If \(W=w\) is a common root at a value of \(U\), the
specialized matrix kills \((1,w,w^2,w^3)^{\mathsf T}\):
the numerator at \(Y=w\) is zero, hence so is the
quotient by \(X-w\). Both determinants \(D_L,D_R\)
therefore vanish at \(U=\theta\) even at specialized
leading-coefficient drops. No fiber is discarded.

Using (5) and \(N\), the exact integer determinant
arithmetic gives degree 24 for each. In ascending order
their reductions modulo 13 are
\[
\begin{aligned}
D_L &: [11,8,6,1,11,10,9,9,3,4,8,0,7,1,1,6,5,6,3,2,10,1,4,11,11],\\
D_R &: [5,2,2,11,12,10,10,11,10,10,4,9,7,4,8,0,11,1,7,11,3,6,4,11,11].
\end{aligned}
\]
In particular neither exact leading coefficient drops.
Bezout coefficient lists in the same order for the two
residue polynomials are respectively
\[
\begin{aligned}
 &[7,4,1,2,11,7,10,11,6,0,4,0,2,8,10,1,10,1,12,0,6,9,4,7],\\
 &[3,10,9,10,12,0,12,0,2,5,0,2,2,10,1,7,9,11,11,6,9,4,9,6].
\end{aligned}
\]
The two products add to 1 in \(\mathbf F_{13}[U]\).
The Lean replay computes both exact integer determinant
lists and trims exact trailing zeros *before* reduction.
It checks degree preservation and the residue identity,
not merely a search at points modulo 13.

If the integer determinants shared a nonconstant rational
factor, its primitive integer form would divide both by
Gauss's lemma. Their leading coefficients are nonzero
modulo 13, so that factor's leading coefficient is too.
Its reduction would be a common nonconstant factor, a
contradiction. Therefore \(D_L,D_R\) are coprime over
\(\mathbf Q\) and have no common root in any characteristic-zero
field. This contradicts the dormant-center system and excludes
the stated ordered four-carrier chart.

The companion file also checks the Gram, affine clock-fit and
polynomial-quotient identities. It does not formalize the
upstream actual-order/reversal/cutoff arguments or the general
field transfer through Gauss's lemma.
