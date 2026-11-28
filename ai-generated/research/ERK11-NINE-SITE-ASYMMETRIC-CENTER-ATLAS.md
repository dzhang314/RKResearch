# Asymmetric two-cross central chart: one full exit and a finite opposite atlas

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
with four distinct calibrations \(a,h=a/2,d=1-b,e=1-b/2\).
Orient the half-choosing front on the left. Its extras are
\(\{e,t\}\); the right extras are \(\{t,s\}\). Thus \(e,t\)
are crossing labels, \(h\) is left-only and \(s\) is
right-only. The dormant is physical 9. This excludes the
matched inner order \(h,s\) and both full affine-zero
fibers over characteristic zero, conditional on genuine
separation and the inherited mixed order conditions.
It reduces the remaining opposite inner order \(s,h\)
to a finite exact clock atlas **without excluding it**.
Asymmetric edge layouts are not covered. Reflection of
an asymmetric edge exchanges which front chooses the
opposite half, not merely the dormant position.

## 1. Bilinear and live two-site reduction

Use the prior models \(V_a,V_b,P,Q,W\) and moments
\(H,C_1,C_2,J_0,I_0,I_1,I_2\). The actual central
four-product equation is
\[
 A_0xy+B_0x+C_0y+D_0=0
\]
with \(x,y\) at physical 8,10, \(z\) dormant at 9, and
\[
 A_0=H^2-J_0I_0,\quad B_0=J_0I_1-HC_1,\quad
 C_0=J_0I_1-HC_2,\quad D_0=C_1C_2-J_0I_2.
\]
The supports and paid grades are precisely those of the
[central two-clock product](ERK11-NINE-SITE-CENTRAL-TWO-CLOCK-RANK-ONE-EXIT.md).
In matched order \((x,y)=(h,s)\) set
\(E=A_0h+C_0,\ N=-(B_0h+D_0)\).
In opposite order \((x,y)=(s,h)\) set
\(E=A_0h+B_0,\ N=-(C_0h+D_0)\).
These equations only license \(s=N/E\) when \(E\ne0\);
the full \(E=N=0\) case is handled below.

In either ordering with \(s\) given, put
\[
 \Pi_5=(X-a)(X-h)(X-d)(X-e)(X-s),\qquad
 m_j=\int_0^1 X(1-X)\Pi_5X^j\quad (0\le j\le3).
\]
In regular order one may multiply \(\Pi_5\) by \(E\)
to get a polynomial with last factor \(EX-N\).
The actual degree-ten scalar tests have surviving
sites \(z,t\), distinct with both modified scalar
weights live. The \(t\) scalar **pool** is nonzero
by the ordinary two-response pair law.
Thus
\[
 d_2=m_0m_2-m_1^2\ne0,\quad d_1=m_0m_3-m_1m_2,\quad
 d_0=m_1m_3-m_2^2,\qquad
 d_2(T-z)(T-t)=d_2T^2-d_1T+d_0.
\]
In particular the exact relations
\(d_2(t+z)=d_1,d_2tz=d_0\) require no optional
shifted pivot or ordering assumption.

The literal derivative characters have coefficients
\(L_0=(a-e)(a-t), L_1=-et\) and
\(R_0=(t-d)(s-d), R_1=-(1-t)(1-s)\), all live.
For regular \(s=N/E\), multiply the right row
by \(E\) in all polynomial operations.
The true first contact \(G(t)=0\) is
\(L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
U_{4,4}(a,b)L_1R_1=0\).

## 2. Repeated-exclusive rows and division-free affine gates

Use the normalized cubic derivative pairings
\(K_j(w)=\langle D_w,D_R^j\rangle_N/[aw(a-w)]\),
\(K_j^R(w)=\langle D_L^j,D_w^R\rangle_N/[b(1-w)(w-d)]\)
from the [preceding edge and middle proofs](ERK11-NINE-SITE-HALF-DIFFERENT-EDGE-EXIT.md).
Put \(k_j=K_j(h)\), \(l_j=K_j^R(s)\), clearing
\(E^3\) in \(l_j\) when needed.
All these division factors follow from the
genuine distinct nonendpoint clocks.
The left-only \(h\) front read is physical third;
the right-only \(s\) front read is reflected sixth
or seventh. Both are actual calibrated response
rows with zero square-clock and primitive reads,
as required by the repeated-exclusive difference.

In matched order \(P_8=Q_{10}=0\). The difference
identities give \(M_L=l_0 L_0+l_1 L_1=0\),
\(M_R=k_0 R_0+k_1 R_1=0\).
Therefore the additional **width-only** equation is
\[
 K=l_1 k_1-T_4(a)l_0 k_1-T_4(b)l_1 k_0+
 U_{4,4}(a,b) l_0 k_0=0 .
\]
This does not assume either derivative pair is
nonzero. Multiply \(K\) by the live \(L_1R_1\)
and use \(l_1L_1=-l_0L_0\) and
\(k_1R_1=-k_0R_0\); the result is \(l_0k_0G(t)\).
The companion Lean file checks this scalar
kernel compatibility over commutative rings.

In opposite order \((x,y)=(s,h)\) the actual
same-clock weighted marks give, before
clearing the \(s\) denominator,
\[
\begin{aligned}
 M_L={}&a I(s,z)(k_0R_0+k_1R_1)
 +30h(a-h)(h-s)(C_1-zH)\langle\ell_a,\Phi_R\rangle_N=0,\\
 M_R={}&b I(h,z)(l_0L_0+l_1L_1)
 +30(1-s)(s-d)(s-h)(C_2-zH)\langle\Phi_L,r_d\rangle_N=0 .
\end{aligned}
\]
These are the literal paired grade-\(4+4+2\)
and primitive grade-\(5+4+1,4+5+1\) masks,
with both active support reads at their true
physical rows. They do not divide by a mixed
amplitude, or assume any individual primitive
is nonzero. All \(I\)'s use the true square
model \(W\) only in the paid integral.

Each marked polynomial is bilinear in \(t,z\).
For \(M=M_{00}+M_{10}t+M_{01}z+M_{11}tz\)
put \(U_M=M_{10}-M_{01}\),
\(V_M=d_2M_{00}+d_1M_{01}+d_0M_{11}\).
Its actual equation implies \(d_2 U_M t+V_M=0\).
Write \(U_L,V_L,U_R,V_R\) for the two pairs.
For \(G=G_0+G_1t+G_2t^2\) put
\(U_G=d_2G_1+d_1G_2,\ V_G=d_2G_0-d_0G_2\).
Then \(U_Gt+V_G=0\).
The necessary remainder polynomials include
\[
\begin{aligned}
 R_{LR}&=U_L V_R-U_R V_L,&
 R_{LG}&=d_2U_L V_G-U_G V_L,\\
 Q_R&=V_R^2+d_1U_R V_R+d_0d_2U_R^2,&
 Q_G&=d_2 V_G^2+d_1U_G V_G+d_0 U_G^2 .
\end{aligned}
\]
The replay also uses the other row pairs and
the other marked norm. These derivations use
only actual affine subtraction and the
two-root nodal polynomial, including if
one or all affine slopes vanish.

## 3. Both full affine-zero branches

For \(E=0\), actual consistency gives \(N=0\),
before any clock solve. The exact \(b\)-resultants
of the two affine coefficients after allowed
width-factor removal have degrees 24 matched
and 32 opposite. Keep \(s\) free in the preceding
polynomial formulas and use each irreducible rational
width quotient. In matched order one cubic
has constant \(b\)-gcd; the other cubic
forces a forbidden width. The degree-6 and
degree-9 width fields have linear \(b\)-gcds.
The first has constant \(s\)-gcd for the true
rank/norm equations; the second has a degree-two
\(s\)-gcd entirely dividing the live \(d_2\).
In opposite order the linear forbidden widths
are \(a=0,2\); the degree-6 and degree-15
fields have linear \(b\)-gcds and constant
\(s\)-gcds. These are exact characteristic-zero
fiber checks, not an assumption of generic
contact coefficients.

## 4. Matched regular exit, opposite regular finite atlas

With \(E\ne0\), the width-only \(K\) is a genuine
necessary equation in matched order.
After removing exact factors only of actual
width and clock guards and the live two-site
\(d_2\), use its \(b\)-resultants with
\(R_{LR},R_{LG},Q_R\). Their exact degrees in
\(a\) are 508, 846, 668.
The deterministic coefficient-bound CRT uses
79 certified primes, reconstructing the
actual rational width projection by the
[integer coefficient method](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-OPPOSITE-EXIT.md).
Its exact common gcd has degree 246, with
irreducibles of degrees \(3,3,6,9\) at
multiplicities \(2,8,12,16\).
The finite fibers are:
\[
\begin{array}{c|c|c}
\text{width degree and multiplicity}&
 \text{forbidden }b\text{-root guard}&
 \text{common factor power}\\\hline
3,2&\text{none needed}&0\\
3,8&b=0&2\\
6,12&E=N=0&3\\
9,16&E=N=0&4
\end{array}
\]
The replay identifies the exact homogeneous
linear roots of the indicated guard pairs,
verifies the raw guard zeros and requisite
Taylor coefficients of all four gates,
and keeps actual \(E\ne0,b\ne0\).
It verifies complete quotient unit ideals
modulo 101 with all leading degrees retained
after reduction in the exact width field.
The maximal-minor finite-free lift then
excludes the whole characteristic-zero
fibers, as in the prior exact edge exits.
This closes the matched central order.

In **opposite regular** order the reduced
\(Q_G,R_{LR}\) have bidegrees \((44,40),(50,45)\)
and exact constant common gcd in \(\mathbb Q[a,b]\).
Two coprime bivariate polynomials have finitely
many common affine width pairs (no common curve,
including a vertical one). For each actual width
\(E\ne0\) fixes \(s\), and the live \(d_2\)
gives at most two choices for \(z,t\) in their
labeled order. Thus this is a finite exact clock
atlas. Its finite residual candidates are **not**
all excluded by this packet.

## 5. General width rank identity for later edge work

The exact scalar factorization of the central
bilinear width determinant is valid for **independent**
\(a,b\):
\[
 633719116800000\,(A_0D_0-B_0C_0)
  =-ab J_0\big(U_{4,4}(a,b)-T_4(a)T_4(b)\big).
\]
Hence an affine double zero forces \(J_0=0\)
or the derivative Gram rank drop, apart from
the forbidden zero widths. Eliminating \(J_0=0\)
by a sign is allowed only over ordered fields
(\(J_0>0\) by the simplex integral).
The replay also checks that
\(A_0^3\{K_1(-C_0/A_0)-T_4(b)K_0(-C_0/A_0)\}\),
read homogeneously as a polynomial, is divisible
by \((U_{4,4}-T_4(a)T_4(b))/(ab)\).
At the forced edge clock \(-C_0/A_0\)
on derivative-rank-one widths, the left
contact coefficients therefore both vanish.
This is a genuine edge fork, not a contradiction
until further paid equations are used.
The exceptional simultaneous \(A_0=C_0=0\)
derivative-width locus projects to a degree-12
single-width polynomial; only that projection
is asserted here.

The standalone replay needs SymPy and python-flint
(verified 0.9). The kernel and affine-zero scalar
identities are in the companion portable Lean
file; actual order payment and the exact
coefficient proofs remain mathematical plus
independent replay. No ordinary stage bound
changes.

See the [standalone replay](erk11-nine-site-asymmetric-center-atlas/replay_n12_asymmetric_center_atlas.py), [exact output](erk11-nine-site-asymmetric-center-atlas/exact-replay.txt), and [portable scalar gate](../lean/RKCert/ReviewedNative/ERK11AsymmetricKernelWidthGate.lean).
