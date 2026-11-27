# Endpoint repeats and linear means are impossible in the ERK10 two-active-pair chart

Over a characteristic-zero field, continue the
[all-live eight-clock ten-active-row chart](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md).
The only two pairs are physical 4/5 at clock \(p=2c_3\)
and physical 10/11 at clock \(q=2c_{12}-1\).
Their genuine grade-three mask \(T=R(c)-r-R(\theta)s\)
has model the polynomial mean \(R\) of degree at most
three and support only on those paired rows and the endpoints.
The two pairs each have different actual amplitudes; \(R\)
is their weighted mean, not either literal amplitude.

**Two additional exact exclusions.** Neither repeated
clock can be an endpoint, and the \(br\)-weighted mean
\(R\) cannot have degree at most one. Both statements hold
over every characteristic-zero field. The generic surviving
means of degree two and three with nonendpoint repeated clocks
are not dealt with here.

## Endpoint clocks

The doubled entrances already give \(p\ne0,\ q\ne1\).
If \(p=1,\ q=0\) simultaneously, the mask supports only
the two numerical endpoints. The paid scalar moments of
\(X(1-X)T\) against degrees through four then give a
nonsingular anchored Gram contradiction to \(R\ne0\).
Suppose just \(p=1\); the case \(q=0\) is its full actual
weighted reflection. The numerical mask supports only
\(0,q,1\). Therefore the anchored polynomial \((X-q)R(X)\)
is orthogonal to degrees through three for the \(X(1-X)\)
measure. The grade count is \(3+3+3=9\) (mask, anchors,
test). If its degree were at most three, this is impossible.
Hence \(R\) is cubic, and after monic normalization
\[
          R(X)=L_4(X)/(42(X-q)),\qquad
          L_4=42X^4-84X^3+56X^2-14X+1 .
\]
In particular \(q\) is one of its four simple roots.

We now use only genuine tests from the
[two-pair model](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md):
the two outer local quadratics for \(x=c_6,1-w=1-c_9\),
the congruence (V), and the ordinary \(7|7\) mixed seam.
The congruence uses
\[
 J_R(X)D_s(X)+\kappa X(X-1)\equiv0\pmod R,\qquad
 D_s=(X-t)(X-x)(X-w)(X-t_R)(X^2+lX+d)
\]
with \(t=p/2,\ t_R=(q+1)/2,\ l=-(y+z),\ d=yz\).
Its derivation cancels the two factors \((X-p)(X-q)\)
from \(D'\) only at **singleton** clocks. Therefore it
remains valid when the repeated clock \(p\) coincides
numerically with the endpoint (the factor \(g(X)\) in
\(J_R\) then has a double zero there).
The scalar seam is the same genuine grade-nine paid
\(\int JP_L\,P_R=0\).

At prime 227 the four distinct residues of \(L_4\) are
24,51,177,204. For each, the two local quadratic leading
divisors are units; their two monic quadratic quotients
cover both physical clock choices simultaneously. In this
full algebra the three-by-three pivot for \(l,d,\kappa\)
in the congruence is a unit. The last monic quadratic
\(Y^2+lY+d\) covers both \(y,z\) orders. In each top
algebra the ordinary paid seam is a **unit**, contrary
to its genuine zero value.

## Degree-one mean

A constant nonzero \(R\) is excluded by the anchored
support Gram through test degree two, as in the base
two-pair note. If \(R\) has degree one, then
\((X-p)(X-q)R\) is an anchored cubic orthogonal to
degrees through two. Take monic \(R=X-a\); the three
clocks \(p,q,a\) are exactly the distinct roots of
\[
                    J_3=14X^3-21X^2+9X-1 .
\]
The true low boundary quadratics still apply: they come
from the degree-three numerical carrier-corrected mask
\(X(X-t)(X-p)\) and its reflection, not from \(\deg R=3\).
The two-step seams are now used rather than the
cubic reconstruction pivot: at actual \(y,z\),
\(\int\bar J^2B_R\ P_L=0,\ \int J^2B_L\ P_R=0\).
Each is affine in only \(y\) or \(z\), respectively.
This use of the actual two-step chronology is why the
lower-degree mean does not require an artificial third
residue of \(R\).

At prime 37, \(J_3\) has distinct residues 12,19,26.
Check all six assignments to \(p,q,a\).
The two local quadratic leading divisors, including the
contact scales, are units in every case. Adjoin both
universal quadratic roots as above. The two affine
coefficients in the two-step seams are units in this
full algebra, so the two equations give \(y,z\) directly,
without another root choice or pivot assumption.
The ordinary paid seam is then a unit in the same
algebra for every branch, a contradiction.

## Replay and field scope

For either subcase, begin with the integral root
algebra of \(L_4\) or \(J_3\) over \(\mathbb Z_{(227)}\)
or \(\mathbb Z_{(37)}\), respectively; the leading
coefficient is a unit and the displayed residues are
distinct. Extend a prime above the specified prime.
The replay only inverts nonzero residue units. Hence
each step can be localized at that prime before
adjoining the next monic roots; no root at infinity
or collapsed quadratic is silently dropped. The
image of each universal quadratic algebra contains
the residue of *either* possible value of its
physical variable, and a unit maps to a nonzero
field value. This proves the contradiction over
any characteristic-zero field, with no ordering.

[ERK10TwoPairFiniteExitGate.lean](ERK10TwoPairFiniteExitGate.lean)
checks the exact anchored moments and split-prime data.
[replay_two_pair_finite_exits.py](replay_two_pair_finite_exits.py)
is a dependency-free exact finite-algebra verification of
the two complete towers, including every asserted unit.
The rooted seam and congruence proofs are the preceding
mathematical reductions using the base two-pair packet.
The unrestricted 14–15 interval is unchanged.
