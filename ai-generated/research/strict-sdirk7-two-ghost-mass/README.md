# A linear Christoffel clock atlas and centered rational exclusion

This packet refines the **seven distinct active clocks, two zero
output weights** order-seven chart developed in the preceding
[two-zero](../strict-sdirk7-two-ghost/README.md) and
[Christoffel](../strict-sdirk7-christoffel/README.md) packets.
Here the adjoint numerator \(W\) vanishes at a nonzero-weight
site \(e\); the site's weight is the required Christoffel mass.
There is no assumption that the active node set is symmetric.

The new atlas reduces the entire regular clock core to one cubic
opener, a linear fourth reverse read, and a quadratic splitting test.
The exception \(e=z/2\) is **ruled out over the rationals**, on both
suffix branches and in every chronological placement. Its arithmetic
openers lie on a positive-rank elliptic curve, but their putative
remaining quadratic never splits, by a uniform five-adic obstruction.
The noncentered rational problem remains open. The packet also includes
an exact new \(\mathbb F_{19}\) tableau with the Christoffel site at the
second active position and verifies all 85 order conditions.

## Kernel representer for the whole clock pencil

Write \(I(X^j)=z^j/(j+1)\), so \(I\) is the uniform functional
on the normalized interval with endpoints 0 and \(z\).
Use \(\mathcal K(x,y)=\sum_{k=0}^3(2k+1)P_k(2x/z-1)P_k(2y/z-1)\).
Put \(g=\mathcal K(e,\cdot)\) and
\(\ell=I-\delta_e/\mathcal K(e,e)\).
Then \(\ell(gP)=0\) for every cubic \(P\), and the radical of
\(\ell\) on the cubic polynomial space is the line through \(g\).
Rational \(\mathcal K(e,y)\) is never zero by the preceding packet.

The six other active clocks have monic node polynomial
\(R_3 S_3\), where \(R_3=(X-1)(X-u)(X-v)\) fixes the last
three sites, and \(S_3\) is monic cubic. The fourth reverse
read is treated separately below. The mass condition is
\(\ell(R_3 S_3)=0\).
For a remaining site \(y\), put \(J_y=\ell(R_3S_3/(X-y))\).
Its original divided-difference numerator satisfies
\(K_y=(y-e)J_y\): subtract the latter expression and use
\(\ell(R_3S_3)=0\).
Writing \(W(y)=\lambda(y-e)\), the three terminal rates
\(r_y=D_y/b_y\) thus pay \(r_y J_y=\lambda\ne0\).
Here \(r_1=-1/2,\ r_u=M/2\), with \(M=u^2-4u+2\); the final
rate is \(r_v=M/2\) on the reflection branch \(v=4-u\)
and \(r_v=MJ/(2T)\) on the arithmetic branch \(v=2u-1\),
where \(T=u^3-7u^2+10u-2,\ J=4u^3-24u^2+39u-17\).

Define the following functional and its uniform representer:
\[
 \nu=\sum_{y\in\{1,u,v\}}\frac{\delta_y}{r_y R_3'(y)},\qquad
 H(X)=\sum_{y\in\{1,u,v\}}\frac{\mathcal K(y,X)}{r_y R_3'(y)} .
\]
All four linear moment rows for \(S_3/\lambda\) now say
\(\ell(S_3 P/\lambda)=\nu(P)\) for all cubic \(P\).
Indeed \(R_3\) and the three quotients \(R_3/(X-y)\) are a basis
of those cubics. Necessarily \(H(e)=\nu(g)=0\).
Conversely if \(H(e)=0\) then \(\ell(HP)=I(HP)=\nu(P)\),
so the entire solution pencil is
\[
 S_3/\lambda=H+t_0 g .
\]
Normalize the leading coefficient to make \(S_3\) monic.
A zero leading coefficient at a candidate is a genuine obstruction,
not a canceled pivot. This represents the hull without a nonlinear
Gram solve or any particular choice of the three early roots.

## Fourth read and rational chronology

If \(e\) is itself the fourth-from-last site, the fourth read is
\(G(e)=0\), where \(G\) is the same reverse function as in the
earlier packet. There is no division by \(W(e)\).
If \(e\) precedes the fourth site \(c\), the three terminal
numbers \(g(y)/r_y\) interpolate an affine \(L\), because \(H(e)=0\).
Interpolation of \(r_y\) gives the quadratic \(q(X)=q_0+q_1X+q_2X^2\).

For any candidate \(c\) among the three \(S_3\) roots,
\(J_c/\lambda=L(c)/g(c)\). To see this, work in the residue algebra
modulo \(g\) and write \(g^{[c]}(X)=(g(X)-g(c))/(X-c)\).
There \(X-c\) has inverse \(-g^{[c]}(X)/g(c)\).
Reducing \((X-c)S_3/(X-c)=S_3\) gives
\[
 g(c)J_c/\lambda=-\ell(R_3\,\mathrm{rem}_g(Hg^{[c]})).
\]
Reduction does not alter \(\ell(R_3 Q_2)\) for quadratics \(Q_2\).
The right side is a polynomial in \(c\) of degree at most two
(at most one when \(g\) is quadratic). At each \(y=1,u,v\)
it equals \(g(y)/r_y\), since \(R_3/(X-y)\) is the corresponding
basis quotient and \(\ell\) annihilates \(g\) times degree at most
three. Thus this polynomial is precisely \(L\).

The definitions and three terminal reverse reads give
\[
 g-qL=\kappa R_3,\qquad G+Eq=\sigma R_3,\qquad
 G L+E g=R_3(\sigma L+\kappa E).
\]
The last identity is native. If \(a_3\) is the cubic coefficient
of \(g\) and \(L_1\) the slope, then \(\kappa=a_3-q_2 L_1\).
Also \(\sigma=2/(3M)\) in reflection and
\(-2q_2(u-1)^3/(3MT)\) in arithmetic, both nonzero on the
rational suffix chart. Consequently the fourth condition at an
early \(e\) is the **linear** equation \(\sigma L(c)+\kappa E(c)=0\).
We keep the possibility of a vanishing linear coefficient in the
general noncentered chart; the centered proof checks that it
cannot occur there. Any valid early candidate has \(\kappa\ne0\):
if \(\kappa=0\), the fourth equation would give \(L(c)=0\)
and hence \(J_c=0\), a zero mass. Thus \(D_c/b_c\ne q(c)\)
at a valid fourth site, so the last-four reverse minor is a unit.
When \(e=c\), \(G(c)=0\) and \(G+Eq=\sigma R_3\) imply
\(q(c)\ne0\), so the same minor remains a unit.

The remaining cubic is
\[
 S_3(X)\ \propto\ H(X)g(c)-g(X)H(c).
\]
If looking for first active forward clock one, choose its reflected
site \(a=z-1\). The root test \(H(a)g(c)-g(a)H(c)=0\) makes the
remaining third root rational automatically. The second active
position can be the Christoffel site (the first cannot be, since the
cubic defect must be visible there). With \(e\) second active and
\(x=z-e\), the forward profile \(h(X)=(X-1)(X-1-t)\)
must satisfy \(Jh(x)=h(x)\), where \(J\) in this sentence
denotes the antiderivative from zero. The exact solution is
\[
 t=\frac{(2/3)(x^3-6x^2+9x-3)}{x^2-4x+2}.
\]
The denominator never vanishes over \(\mathbb Q\); the numerator is
nonzero by Eisenstein at 3. The two-profile minor is nonzero
except \(x=0,1,3\), since
\(M(x)(x-1-t)=x^2(x-3)/3\). These are chronological tests
for this particular first-active clock, not restrictions imposed on
every method. The finite control below verifies their regularity.

## No centered rational clock core

Let \(m=z/2=e\). Up to scale \(g(X)=5X^2-10mX+2m^2\).
For a general cubic \(g=\sum a_i X^i\), the reflection opener
factor reduces to \(a_0+a_1+2a_2+6a_3=0\), independently of \(u\).
At the center it forces \(m^2-5m+5=0\), impossible rationally.

For arithmetic the opener becomes
\[
 A m^2+B m+C=0,\quad
 \begin{cases}
 A=(u-3)(2u^2-10u+11),\\
 B=-5(u-3)(u-2)(2u-3),\\
 C=10(u-2)^2(u-1).
 \end{cases}
\]
Its exact discriminant is \(5(u-3)(u-2)^2(4u^3-24u^2+57u-47)\).
Set \(w=(2Am+B)/(u-2)\), \(X=80/(u-3)\) and \(Y=X^2w/80\).
The native scalar transfer gives
\[
 Y^2=X^3+105X^2+4800X+128000 .
\]
Conversely the same formulas recover \(u,m\) on the allowed
chart. The curve has no rational torsion by its good reductions
with \(13,12\) points at 13 and 17, respectively. Thus the point
\((-40,200)\) is nontorsion. Its double \((-16,-272)\) and the
opposite point give \(u=-2,\ m=12/13\) or \(8/3\), with fourth
sites \(11/5\) or \(123/25\), respectively. This illustrates
the rational opener family, not a tableau.

If the center is itself fourth, combine \(G(m)=0\) with the
quadratic. The exact resultant has the factors \((u-3)^2
(u-2)^2(u-1)^3\) and a primitive octic projectively rootless mod 13.
A separate noncentered example, the known fourth point
\((u,e)=(53/31,11)\), gives a primitive sextic in \(m\)
projectively rootless mod 17. No full noncentered fourth exclusion
is claimed.

For an earlier center, the exact symbolic function field replay
checks all rational pivots. In particular the norm of the fourth
slope has, up to a nonzero scalar and denominator, factors
\[
 X^4(X+40)^2(X+80)^4(X^2-160X-12800)^2
 (X^3+96X^2+3840X+102400).
\]
The linear zeros are excluded \(u=1,2\) or outside the affine
coordinate. The quadratic and cubic are projectively rootless
mod 7 and 17. The fourth clock is therefore uniquely rational.

For clarity, the splitting calculation uses centered coordinates
\(x=(y-m)/m\) and \(\rho=3/5\). In them \(\ell\) has moments
\((5/9,0,1/3,0,1/5,0,1/7)\) and \(x^2-\rho\) is its radical
factor. Let \(N+Kx\) be the remainder of monic \(S_3\) modulo
\(x^2-\rho\). Pairing it against the first two terminal quotients
determines \(N,K\) up to scale, and the mass condition fixes
the scale by \(\ell(R_3(N+Kx))=-4/175\):
indeed \(\ell(R_3 x(x^2-\rho))=4/175\).
The first two quotient classes are independent modulo the
radical factor: the third suffix factor is invertible there,
and the two distinct remaining linear factors are independent.
Writing the centered fourth clock as \(c'\), the remaining two
root polynomial is
\[
 x^2+q_1x+q_0,\quad
 q_1=-(Kc'+N)/(c'^2-\rho),\quad q_0=K-\rho+c'q_1 .
\]
This prescription uses only exact rational operations.

The replay computes \(\Delta=q_1^2-4q_0\) in the elliptic
function field. Its denominator is a polynomial square,
with degree-3 and degree-12 constituent factors rootless over
\(\mathbb Q\) modulo 19 and 7 respectively. On removing that
square, its numerator is
\((A_*(X)+B_*(X)Y)/(5\cdot 2023^2)\),
where \(A_*,B_*\) are explicit integers of degrees 30 and 28.
Thus splitting requires \(5(A_*(X)+B_*(X)Y)\) to be a rational square.

Write \(X=a/d^2,Y=b/d^3\) with integral \(a,b,d\) and coprime
\(a,d\). These are the ordinary primitive weighted elliptic
coordinates: a negative valuation of \(X\) makes \(X^3\) the
unique lowest-valuation curve term, so the valuation of \(X\)
is even and the denominator of \(Y\) has the required cube.
After multiplication by the square \(d^{60}\), the split
test is an integral square equation with right side \(5N(a,b,d)\).
The checked coefficient data give \(N(a,b,d)\equiv2a^{30}\pmod5\).
An integral square divisible by 5 is divisible by 25;
hence \(5\mid a\) and \(5\nmid d\), without losing nonintegral
\(X\). The curve also gives \(5\mid b\). Write \(a=5a_0,b=5b_0\).
The scaled curve forces
\(b_0^2=5(a_0^3+21a_0^2d^2+192a_0d^4+1024d^6)\).
Therefore \(b_0=0\pmod5,\ a_0/d^2=2\pmod5\); the cubic
\(U^3+21U^2+192U+1024\) has only the root 2 modulo 5.

The exact coefficient scaling is \(N(5a_0,5b_0,d)=5^{30}N_5(a_0,b_0,d)\),
and the scaled residue then equals \(2d^{60}\ne0\bmod5\).
The putative square has odd five-adic valuation 31, a contradiction.
The entire primitive-integer contradiction, including all modular
unit/denominator cases, is checked by
[no_primitive_square](../../lean/RKCert/Research/SDIRKSevenChristoffelCentered.lean).
The independent symbolic script regenerates its literal coefficients
from the moments; the field-function reduction and graded ingress
are written mathematical arguments, not a native HasOrder wrapper.

## Second-active finite control and replay

The exact literal \(\mathbb F_{19}\) tableau has reciprocal
diagonal 6, active reflected clocks \((5,16,13,0,17,9,1)\),
and \(t=9\); \(e=16\) is its second active site. Its exact
eighth-bush residual is 15. Native Lean checks the mask, unit
diagonal, all 85 conditions, and the next-order failure.
The atlas checks \(H(e)=0\), the cubic roots \((0,5,13)\),
the unique fourth root \(c=0\), and the two-profile helper.
Its two reduced equations \(H(e)=S_3(z-1)=0\), using the
unnormalized cubic numerator, have Jacobian columns
\((18,13),(10,0),(6,5)\) in \((z,u,e)\) modulo 19.
All three minors are nonzero. This is a regular finite control,
not a rational lift.

Run the independent scripts in this directory:

    python check-centered.py
    python check-fourth-placement.py
    python check-f19.py
    python check-atlas-jacobian.py

The first uses python-flint 0.8, the second SymPy 1.14, and the
finite replays use standard Python. Then build the two Lean
modules with the earlier Christoffel module available and run the
typed audit. The native checks were run under stock Lean 4.36.0.

The [reflection-suffix follow-up](../strict-sdirk7-mass-reflection/README.md) excludes the entire rational reflection suffix in this same Christoffel-mass chart, independent of the center or the first active clock.

For the arithmetic suffix, the [five-adic follow-up](../strict-sdirk7-mass-arithmetic-at-five/README.md) excludes an integral penultimate clock reducing to zero modulo 5. Other residue classes remain, and an exact local clock core shows that the scalar splitting condition is not globally obstructed at 5.

Two [alternate first-active schedules](../strict-sdirk7-mass-first-clock/README.md) remove one forward tap equation and give two more native exact characteristic-19 controls. The matching rational endpoint cuts are excluded, not the full arithmetic chart.
