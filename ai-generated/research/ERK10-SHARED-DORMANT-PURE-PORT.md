# The shared-dormant ERK10 chart localizes a genuine fifth-grade pure port

Work over any characteristic-zero field in the
[all-live two-carrier equality ledger](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
and [eight-label census](ERK10-THREE-CARRIER-EXCLUSION.md).
There are eight distinct, singleton r-active rows, two additional
noncarrier r-dormant rows \(i<j\) at one common clock
\(\zeta\notin\{0,1\}\), and the original first and last rows.
The two carriers are physical 2 and 13 at a common clock \(\theta\)
with indicator \(s\) and opposing weights. The active profile is
\(r=As\); for the scalar calculations rescale this vector by a
nonzero constant so that its active value is \(R(c)\), where
\[
          R(X)=L(X)/(X-\zeta),\qquad
          L=42X^4-84X^3+56X^2-14X+1 .
\]
This normalization is the actual paid cubic fit for this shared
clock, by the anchored \(X(1-X)(X-\zeta)\)-Gram argument in the
eight-label census. Hence \(L(\zeta)=0\), and \(R\) has three
simple roots, distinct from \(\zeta\) and the endpoints.
The active clocks can still coincide with \(\zeta,0,1\) numerically;
their physical stages are different and are not counted as dormant.

**New necessities.** Both dormant rows are in physical positions
6 through 9. Both orientations have one and the same fifth-grade
pure complement to \(s+r\mathcal P_{\le2}(c)\), and it can be chosen
supported exactly on the two dormant rows. In either orientation
its true unary advance has a calibrated polynomial restriction of
degree at most six on the eight active clocks. At least two active
responses are nonzero; if exactly two, their clocks are the shared
dormant clock and the relevant outgoing endpoint. This does not
exclude the remaining chart.

## Endpoints and the two measured dormant taps

Use the actual grade-three mask
\[
             T=R(c)-r-R(\theta)s .
\]
It has model \(R\) and support exactly at physical \(1,i,j,14\).
In particular \(U=(C-\zeta)T=e_1+e_{14}\) has grade four and
model \(L\). The paid moments with \(1,C\) give
\(b_1=b_{14}=1/30\). Pairing \(U\) with all of \(F_5\) costs
nine and makes the forward terminal point exact through grade
five (every pure vector vanishes at the origin). The full all-live
weighted reverse has the same numerical \(E_4\); the same
argument gives its terminal point exactness through five.
Thus both orientations are point exact through grade five at both
physical endpoints. Their common numerical \(E_5\) now has the
same formal polynomial map as well: the two grade-five models
of an \(E_5\) vector have the same first five moments, and their
difference vanishes at the physical origin. Factoring \(X\) and
testing through degree four gives the nonsingular anchored Gram.
Consequently \(F_5\) is **common** to both orientations.
The exact grade-five test \(A U=Ae_1\) at physical 14 gives
\(A_{14,1}=\int_0^1 L=1/15\).

The pooled dormant mass \(b_i+b_j\) is the nonzero canonical
Lobatto weight at \(\zeta\): compare \(bT=\int R\) to the exact
six-node Lobatto rule, where \(R\) vanishes at the other three
interior nodes. The endpoints have just been calibrated.
This weight is nonzero in characteristic zero, e.g. by evaluating
the exact rule on \(X(1-X)R^2\), whose integral is positive in
the real splitting field and remains nonzero algebraically.

The only possible physical term of the genuine degree-nine
product \((C-1)T\cdot A(CT)\) is at \(j\). Exactness gives
\[
 b_j A_{ji}\,\zeta(\zeta-1)R(\zeta)^2
 =\int_0^1 J[XR](X)(X-1)R(X)\,dX
 =\frac{105\zeta(1-\zeta)-56}{1800}.
\]
The scalar evaluation is direct polynomial division:
for \(R=42X^3+(42\zeta-84)X^2+
(42\zeta^2-84\zeta+56)X+42\zeta^3-84\zeta^2+56\zeta-14\)
the integral before reduction is
\[
 -147\zeta^6/2+441\zeta^5/2-2597\zeta^4/10+
 1519\zeta^3/10-5509\zeta^2/120+161\zeta/24-343/900.
\]
Reduction modulo \(L(\zeta)\) gives the displayed fraction.
It is nonzero even without an order: at \(t=\zeta(1-\zeta)\)
the quartic becomes \(42t^2-14t+1\), which does not vanish
at \(t=8/15\), by the displayed integer norm in the companion.
Thus \(A_{ji}\ne0\). The exact grade-four \(AT\) reads at
the two dormant rows give
\[
 A_{i1}=JR(\zeta)/R(0),\qquad
 A_{j1}=A_{i1}-A_{ji}R(\zeta)/R(0),
\]
and reflection gives the opposing two terminal tap identities.
We do not use equality of the two grade-five offcore
projections as a second independent equation in the weight
split: it reproduces the same pooled constraint.

## The actual fifth-degree dormant port

Let \(z\in F_5\setminus (Ks+r\mathcal P_{\le2}(c))\).
The active restriction of \(E_5\) is the annihilator of \(br\)
and \(bCr\) on the eight active rows, of rank six by the
all-live equality ledger. The polynomials of degree at most
five already give exactly this rank on eight distinct clocks;
thus the active profile of \(z\) is a polynomial \(Z\) of
degree at most five. The endpoints of \(z\) are zero by the
just-proved point exactness. Its carrier entries agree
numerically and cancel (every \(E_5\) vector agrees there).
Pairing the actual \(T\) with \(z\) costs eight and gives
\(b_i z_i+b_j z_j=0\), since \(R(\zeta)\ne0\).
It follows that the five ordinary moment equations for \(z\)
reduce to
\[
    \sum_{k\ {\rm active}}
       \frac{x_k^a Z(x_k)}{R(x_k)D'(x_k)}=0,\qquad 0\le a\le4,
 \quad D(X)=\prod_{k\ {\rm active}}(X-x_k).
\]
Here \(br=\kappa/D'\), \(\kappa\ne0\), by the eight-label
barycentric identity. Divide \(Z/R\) into its polynomial
part (degree at most two) and simple fractions at the three
roots \(\rho\) of \(R\). The polynomial part is killed by
the leading coefficient identity, since its product with
\(X^a\) has degree at most six. For a simple fraction,
\[
       \sum_{k\ {\rm active}}
       \frac{x_k^a}{(x_k-\rho)D'(x_k)}
              =-\frac{\rho^a}{D(\rho)} .
\]
For \(a=0\) this follows from partial fractions of \(1/D\);
for \(a\ge1\) divide \(x_k^a-\rho^a\) by \(x_k-\rho\) and
use the same leading coefficient identity. The \(D(\rho)\)
are units since no active \(R(x_k)\) vanishes.
The first three moments of three distinct roots now force
all residues of \(Z/R\) to vanish. Therefore \(Z=R P_2\).

Subtract \(r P_2(c)\) and the common carrier component from
\(z\). The resulting genuine nonzero pure grade-five vector,
again called \(z\), is supported on \(\{i,j\}\), with
\(b_i z_i+b_j z_j=0\). Nonzeroness of both weights and of
\(b_i+b_j\) proves \(z_i,z_j\ne0\) and \(z_i\ne z_j\).
Thus the two actual stages first separate **at grade five**:
through grade four their defect evaluations are zero and they
share the clock.

## Literal row 5 or row 10 cannot be dormant

The local entrance computation in the
[two-carrier ledger](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
uses only \(F_4=\langle s,r,Cr\rangle\), not the later
two-active-label hypothesis. Its first two active rows
are physical 3,4. In unscaled physical time put \(t=c_3\),
\(x=c_4\). The actual outgoing amplitudes
\(A_{32},A_{42}\) are
\[
          t^2/(2\theta),\qquad x^2(3t-2x)/(2\theta t).
\]
If physical row 5 is dormant, it has no tap on carrier 2
and its clock \(u=\zeta\ne0\). Write
\(a=A_{53},b=A_{54}\). Its exact primitives on \(c^2,c^3\)
and \(Ar=0\) there give
\[
 a t^2+b x^2=u^3/3,\quad a t^3+b x^3=u^4/4,\quad
 a t^3+b x^2(3t-2x)=0.
\]
The third left side is three times \(t\) times the first
left side minus twice the second. Thus \(u=2t\).
The cubic \(X(X-t)(X-x)\) literally vanishes on all other
predecessors, and the carrier tap is zero; its paid primitive
forces \(x=2t=u\). This does not by itself rule out a
numeric active–dormant clock collision. It does force the
two active amplitudes to have ratio \(-4\).
The fitted \(R\) then requires \(R(\zeta)=-4 R(\zeta/2)\),
equivalently
\(\zeta L'(\zeta)=8L(\zeta/2)\). In characteristic zero this
is impossible: clearing by 2 gives the polynomial
\[
    P(X)=294X^4-336X^3+84X-16
\]
with the exact certificate
\[
 (-319284X^3+182028X^2+95802X-35007)L+
 (45612X^3-65100X^2+24738X-2263)P=1201 .
\]
The reflected argument applies to literal row 10, since
\(L\) is symmetric and \(r^\star\) is a nonzero multiple
of \(r\). The first and last two middle rows were already
active, hence both dormant rows belong to 6 through 9.

## The two actual degree-six responses

Let the degree-at-most-six polynomials for the active
restrictions of \(Az\) and \(A^\star z\) be \(P_R,P_L\).
These exist because \(Az\in F_6\), \(A^\star z\in\bar F_6\)
and the numerical degree-six spaces agree. Their common
active restriction is \(\operatorname{Ann}(br)\) of dimension
seven, equal to the evaluations of polynomials through degree
six. No identification of the two *pure* grade-six spaces is
needed. Put
\[
        m_R=b_j A_{ji} z_i,\qquad
        m_L=b_i A^\star_{ij} z_j .
\]
These nonzero scalars are the total dormant masses of the
two respective unary responses, by strictness.
The actual forward endpoint at row 1 has zero \(Az\);
the reverse one at row 14 has zero \(A^\star z\).
In each case their carrier values cancel.
The pure degree-six scalar moments through degree three can
be split by the same partial fractions as above. The polynomial
part now has degree at most three, and its product with the
testing monomial still has degree at most six. Consequently
the four moments are exactly those of a row supported at the
three roots \(\rho\) of \(R\), at \(\zeta\) with mass \(m_R\)
or \(m_L\), and at the opposite endpoint \(1\) or \(0\).
The contribution at a root is
\(-\kappa P_R(\rho)/(R'(\rho)D(\rho))\), or the same for
\(P_L\). Each five-site row is uniquely determined by its
nonzero mass at \(\zeta\) (the one-dimensional barycentric
nullspace). Comparing these masses gives the exact residues
\[
 \frac{P_R(\rho)}{D(\rho)}
   =-\frac{m_R(\zeta-1)R(\zeta)}
             {\kappa(\rho-1)(\rho-\zeta)},\qquad
 \frac{P_L(\rho)}{D(\rho)}
   =-\frac{m_L\zeta R(\zeta)}
             {\kappa\rho(\rho-\zeta)} .
\]
All factors used in these divisions are nonzero. In particular
both degree-six polynomials are nonzero. Hence on eight distinct
active clocks each response has at least two nonzero occurrences.

If the forward response has exactly two nonzero active
values at \(x_a,x_b\), its polynomial has exactly six distinct
active roots and degree six. Then
\(P_R(X)/D(X)=k/[(X-x_a)(X-x_b)]\) with \(k\ne0\).
The three displayed residue tests make the two quadratic
denominators proportional (their cross difference of degree
at most two has three distinct roots). Since both are monic,
\(\{x_a,x_b\}=\{1,\zeta\}\). Reflection proves
\(\{0,\zeta\}\) if the reverse response has exactly two.
Outside these precise clock collisions each direction requires
at least three active responses. These are actual marked
contrasts across the two physical dormant rows, not conditions
on a compressed or artificially merged column.

## Entire pure flags through grade seven and an extreme causal gate

The paid \(T\cdot Az\) test has grade \(3+6=9\).
Only the dormant mass \(m_R\) and physical terminal contribute,
so
\[
 b_{14}(Az)_{14}=-m_R R(\zeta)/R(1)\ne0 .
\]
Similarly \(b_1(A^\star z)_1=-m_L R(\zeta)/R(0)\ne0\).
The common span \(Ks+r\mathcal P_{\le3}(c)+Kz\) has rank six
and vanishes at both physical endpoints. By the exact rank-seven
pure flags this proves
\[
 \begin{split}
 F_6&=Ks+r\mathcal P_{\le3}(c)+\langle z,Az\rangle,\\
 \bar F_6&=Ks+r\mathcal P_{\le3}(c)+\langle z,A^\star z\rangle .
 \end{split}
\]
Their intersection is the six-dimensional common span.
One grade later start with the rank-seven space
\(Ks+r\mathcal P_{\le4}(c)+Kz\). The actual \(Az\) raises rank
by its nonzero terminal value. The combination \((C-1)Az\)
vanishes at both endpoints but has nonzero pooled dormant mass
\((\zeta-1)m_R\), unlike every vector in the starting span.
Hence, with the reflected argument,
\[
 \begin{split}
 F_7&=Ks+r\mathcal P_{\le4}(c)+\langle z,Az,CAz\rangle,\\
 \bar F_7&=Ks+r\mathcal P_{\le4}(c)+\langle z,A^\star z,CA^\star z\rangle .
 \end{split}
\]
The dimension equals nine in both cases by the paid alias ledger.
There is no assumption of identical pure flags in these grades.

Suppose the two dormant positions are the extreme late consecutive
pair \(i=8,j=9\). Put \(w=Az\).
In the actual grade-seven expansion of \(Aw=A^2z\), the \(s\)
coefficient is zero by physical row 2 and the \(z\) coefficient
is zero at physical row \(i\). There \(w_i=0=(Aw)_i\) and
\(z_i\ne0\). At row \(j\), strictness and adjacency make
\((Aw)_j=0\), while \(w_j=A_{ji}z_i\ne0\); therefore the
affine coefficient of \(w\) has its root at \(\zeta\).
Finally on the five earlier distinct active clocks physical 3–7,
both \(Aw\) and \(w\) vanish, so the degree-at-most-four
polynomial coefficient of \(r\) is identically zero. Thus
\[
                   A^2 z=\eta(C-\zeta)Az
\]
for a scalar \(\eta\), which has not been shown nonzero.
The reflected counterpart holds for \(i=6,j=7\). These conditions
do not dispose of the four other possible middle placements,
or even of these two extreme placements.

[ERK10SharedDormantGate.lean](ERK10SharedDormantGate.lean)
checks the exact algebraic first-contact norm, paired cancellation,
and three-root tests. The polynomial division and stage-profile
reductions above are mathematical. The remaining literal middle
support chart is not excluded, and the unrestricted ERK10 interval
is unchanged.
