# Nine live sites: the four-distinct three-cross central layout is impossible

**Scope.** The [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
has four distinct calibration clocks \(a,h=a/2,d=1-b,e=1-b/2\).
The left and right extras are \(\{e,t\}\) and \(\{h,t\}\),
so \(h,e,t\) are the three crossing pairs. The dormant
row is physical 9, and the other free active label \(u\)
fills physical 8 and 10. This excludes the layout over
**characteristic zero** under genuine separation and
the inherited actual mixed order payments. Together with
the [edge result](ERK11-NINE-SITE-DISTINCT-THREE-EDGE-EXIT.md),
all three dormant positions of this particular geometry
are closed. Other four-distinct overlap types and the
ordinary ERK11 stage bound are not settled here.

## 1. Actual central marks, with no centroid sign assumption

Use \(V_a=X^2(X-a)^2,\ V_b=(1-X)^2(X-d)^2\),
\(P=JV_a,\ Q=\bar J V_b,\ W=V_aV_b\), and
\[
 H=\int PV_b=\int V_aQ,\quad C_1=\int XPV_b,\quad
 C_2=\int XV_aQ,\quad J_0=\int PQ,\quad I_j=\int X^jW .
\]
Every integral without displayed endpoints is over \([0,1]\).
The literal unadvanced product \(V_LV_R\) is supported
on physical \(8,9,10\); its two non-dormant coordinates
have the same clock \(u\). Its paid masks \(X-u\)
and \(X(X-u)\) (total grades \(9,10\)) give
\[
 M=I_1-uI_0,\quad N=I_2-uI_1,\quad N=zM,\quad
 I=I_2-2uI_1+u^2I_0=N-uM .
\]
Here \(z\) is the actual dormant clock. The doubly
masked product has literal value
\(I=b_9(z-u)^2 V_a(z)V_b(z)\ne0\).
Thus \(I=(z-u)M\) proves \(M\ne0\) and \(z=N/M\)
over any characteristic-zero field. No sign of the
width or an unproved rank of a moment matrix is used.

The [four-product central identity](ERK11-NINE-SITE-CENTRAL-REPEATED-PAIR-IDENTITY.md)
is
\[
 \mathcal L(u)=(C_1-uH)(C_2-uH)-J_0 I=0.
\]
It uses the actual support intersection at row 9
and the paid grades \(5+4+1,4+5+1,5+5,4+4+2\).
The literal mixed primitive amplitudes further imply
\[
 P_9=(C_1-uH)V_a(z)/M,\qquad
 Q_9=(C_2-uH)V_b(z)/M .
\]
For example, \(I P_9=(C_1-uH)(z-u)V_a(z)\)
follows from the masked products, and the actual live
\(z-u\) cancels using \(I=(z-u)M\).
This avoids any division by \(C_i-uH\) or \(J_0\).

As an independent finite-atlas check, the full three
coefficients of \(\mathcal L=A u^2+B u+C_0\)
never vanish simultaneously in characteristic zero:
their three pairwise \(b\)-resultants have exact \(a\)
degrees \(32,28,26\) and constant common gcd. The
final exclusion below does not need either the
degree-two leading coefficient or \(H\) to be
nonzero for a general projected width.

## 2. Four scalar/Gram equations and their width norms

Set
\[
 \Pi_5=(X-a)(X-h)(X-d)(X-e)(X-u),\qquad
 m_j=\int_0^1 X(1-X)\Pi_5 X^j \quad (0\le j\le3).
\]
These are true ordinary quadrature tests of degree
at most ten. The only surviving sites are \(z,t\),
both with live modified weights because the nine
ordinary clock sites and their scalar **pools**
are genuine and live. The \(t\) pool is live by the
six-pair response law, not merely individual weights.
Write \(e_j=M m_{j+1}-N m_j\), \(j=0,1,2\).
Then \(e_0\ne0\) by the surviving \(t\) term,
\(t=e_1/e_0\), and the two true shifted tests give
\[
 D=e_0e_2-e_1^2=0 .
\]
No third shifted row is paid or used. Using \(t=e_1/e_0\)
clears the live factor \(e_0\) in the left and right
derivative factors:
\[
 L_0=(a-e)(a e_0-e_1),\quad L_1=-e e_1,\qquad
 R_0=(h-d)(e_1-d e_0),\quad R_1=-(1-h)(e_0-e_1).
\]
Their actual off-diagonal is \(F=0\), with
\(F=L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
U_{4,4}(a,b)L_1R_1\).

For the scalar support equation, put
\(I_H=\int X(X-1)(X-t)\Pi_5\).
The true degree-eight Lagrange weight at \(z\)
and the actual \(I\) give
\[
 I(z-h)(z-e)(z-t)
   = I_H z(z-1)(z-a)(z-d)(z-u).
\]
All canceled clock differences are live. Inserting
\(I=(z-u)M\) and clearing the earned denominators
gives
\[
 A_{\rm mask}=
 M^2(N-hM)(N-eM)(e_0 N-e_1 M)
 +(e_0m_1-e_1m_0)N(N-M)(N-aM)(N-dM)=0 .
\]

For the last equation use the **actual** dormant
reciprocal Gram diagonal. Write \(D_z=a^5\ell_z-
30P(z)\ell_a,\ D_z^R=b^5r_z-30Q(z)r_d\).
Since the dormant response is zero, its two anchored
rows are literally scaled by
\[
 \begin{aligned}
 L^\# &= M^5 D_z+
       30(C_1-uH) N^2(N-aM)^2\ell_a,\\
 R^\# &= M^5 D_z^R+
       30(C_2-uH)(M-N)^2(N-dM)^2r_d.
 \end{aligned}
\]
They are \(a^5M^5\) and \(b^5M^5\) times
the actual respective row-9 anchored functionals,
as follows from the primitive reads above and
\(P(a)=a^5/30,\ Q(d)=b^5/30\).
With the normalized integer inverse Gram \(N_{\rm G}\),
the equation is
\[
 B_{\rm diag}=210\langle L^\#,R^\#\rangle_{N_{\rm G}}
 -a^5b^5 I\,N^2(N-aM)^2(M-N)^2(N-dM)^2=0.
\]
Indeed the unscaled actual Gram pairing is \(1/b_9\);
the square-clock support formula gives
\(1/b_9=I W(z)/M^2\).
The right side above is not an asserted
dormant point-exactness condition.

All \(D,F,A_{\rm mask},B_{\rm diag}\) are polynomials
in \(a,b,u\). Remove no factor from \(D\),
\(ab\) from \(F\), \(M\) from \(A_{\rm mask}\),
and \(a^3 b^3N(N-M)(N-aM)(N-dM)\) from \(B_{\rm diag}\).
These are exact divisions by live factors.
Take the four \(u\)-resultants with the raw
\(\mathcal L\), using the finite actual root \(u\).
They are symmetric in \(a,b\), checked exactly.
Reflection exchanges the two fronts and sends
\(u,z,t\) to \(1-u,1-z,1-t\); the paired discrete
tests and symmetric derivative Gram agree with this
coefficient check. The four norms have bidegrees
\((32,32),(40,40),(50,50),(52,52)\).
The first two are coprime over \(\mathbb Q\);
their finite algebraic width atlas alone would not
already be an exclusion.

## 3. Exact symmetric width projection

Use symmetric variables \(s=a+b,\ w=ab\).
Each symmetric monomial pair is rewritten via
\(P_0=2,\ P_1=s,\ P_j=sP_{j-1}-wP_{j-2}\) for
\(P_j=a^j+b^j\), times the appropriate power of \(w\).
This does not divide by \(a-b\), which can vanish.
The only additional allowed symmetric cancellations
are exact powers of the width guards
\(s-1,s-2,w,w-s+1,w-2s+4,w+2(s-2)(s-1)\).
They come respectively from the required distinct
calibration clocks and nonendpoint widths.
The four resulting bidegrees in \((s,w)\) remain
\((32,32),(40,40),(50,50),(52,52)\).

The three \(w\)-resultants of the first norm with
the other three have exact \(s\)-degrees
\(1264,1568,1632\). The integer input coefficient
\(\ell^1\)-determinant bounds have bit lengths
\(11934,14732,15528\).
The exact CRT uses 255 certified primes with
modulus product greater than twice every bound.
The method is the one in the
[opposite half–half central exit](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-OPPOSITE-EXIT.md);
no unknown tableau is reduced modulo a prime.
The exact monic common gcd is
\[
 W_4(s)^8 W_{12}(s)^4 \quad\text{(degree 80)} ,
\]
where \(W_4\) is the monic normalization of
\(165s^4-264s^3+156s^2-40s+4\), and \(W_{12}\)
is the monic irreducible degree-twelve factor
of the following exact low-degree resultant.
Use the two symmetric width polynomials
\[
 \mathcal Z=I_0I_2-I_1^2,\qquad
 \mathcal T=(C_1I_0-HI_1)(C_2I_0-HI_1).
\]
Their \(w\)-resultant has degree 28 and a unique
degree-twelve irreducible factor.
Every actual finite \(s,w,u\) must lie on one
of the two projected width factors; the remaining
tests check true fibers, not just separate norm roots.

## 4. Complete two-stage width/clock fiber checks

**At \(W_4=0\).** The four symmetric norms are
exactly divisible by \(w^2\) in the complete monic
width coefficient algebra. Removing that factor
leaves constant gcd in both residue coefficient
fields of degrees \(1,3\) modulo 101, with all
leading degrees retained. The finite-free
multiplication-map argument lifts the unit ideal.
The only possible original root \(w=0\) violates
the true \(a,b\ne0\).

**At \(W_{12}=0\).** Compute the exact homogeneous
linear \(w\)-subresultant \(\lambda w+\eta\) of
\(\mathcal Z,\mathcal T\). Its leading coefficient
\(\lambda\) is a unit in the whole coefficient
reduction modulo 101. Exact homogeneous evaluation
verifies \(\mathcal Z=\mathcal T=0\) at
\(w_0=-\eta/\lambda\).
The four symmetric norms divide exactly by
\((w-w_0)^2\) after reducing the width; their
quotient gcd is constant in each complete residue
coefficient field of degrees \(3,4,5\) modulo
101, with all leading degrees retained.
The same finite-free lift proves \(w=w_0\).

For clarity these lifts take place over the
localized coefficient algebra
\(\mathbb Z_{(101)}[s]/(W_i)\). The monic width
polynomial makes it finite free; the tested
determinants of multiplication give the required
unit denominators. A polynomial retaining its
leading coefficient in every residue factor
can be made monic. Its finite-free power basis
allows a maximal unit minor test for the maps
multiplying by the other quotient polynomials.
Thus a verified unit ideal modulo 101 in the
whole coefficient algebra yields the
characteristic-zero unit ideal. There is no
inference from arbitrary unknown stage
denominators becoming nonzero modulo 101.

In the degree-twelve case, the actual widths
\(a,b\) are the two roots of \(X^2-sX+w_0\),
with \(b=s-a\). Adjoin \(a\) by that monic
quadratic to the same localized coefficient algebra.
The replay checks **all 24** residue embeddings:
both roots over each of the twelve \(s\)-roots.
There \(I_0\) and the leading quadratic coefficient
\(A\) of \(\mathcal L=A u^2+B u+C_0\) are units.
This earns both units in the complete coefficient
algebra over the localized integers.

Set \(u_0=I_1/I_0\). The exact identities
\(\mathcal Z=\mathcal T=0\) imply
\(I_0 I_2=I_1^2,\ \mathcal L(u_0)=0\).
Thus the live pivot \(M=I_1-uI_0\ne0\) means
\(u-u_0\ne0\), and the actual \(\mathcal L\)
gives the affine quotient
\[
 \Lambda=I_0 A u+I_0 B+A I_1=0 .
\]
Also \((M,N)=-(u-u_0)(I_0,I_1)\).
Cancel the square of \(u-u_0\) from \(D,F\)
by using modified moments
\(I_0 m_{j+1}-I_1 m_j\) in their exact formulas.
This replacement introduces only a common scale,
and does not assume a new order condition.
In every one of the 24 residue embeddings the
affine polynomial \(\Lambda\) retains its unit
leading coefficient, and its gcd with both
modified equations is constant. The finite-free
lift eliminates the entire true \(u\)-fiber
over characteristic zero. There is no sign
or nonzero-variance assumption: the spurious
variance-zero projected width is explicitly
checked.

The standalone replay needs SymPy and python-flint
(verified 0.9) and includes the complete deterministic
integer reconstruction and the width/clock lifts.
ERK11CentralVarianceFactorGate.lean checks the
arithmetic of the masked primitive cancellation,
the zero-variance factor, the quadratic quotient, and
reflection over arbitrary commutative rings.
The stage transfer, rooted-order payment and exact
elimination remain mathematical plus replay, not an
end-to-end native Lean tableau theorem.

See the [standalone replay](erk11-nine-site-distinct-three-center-exit/replay_n12_distinct_three_center_exit.py), [exact output](erk11-nine-site-distinct-three-center-exit/exact-replay.txt), and [portable Lean gate](../lean/RKCert/ReviewedNative/ERK11CentralVarianceFactorGate.lean).
