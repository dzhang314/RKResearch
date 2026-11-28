# Nine live sites: no half–half identical-extra edge-dormant layout

**Scope.** Continue the [genuine nine-site six-pair remainder](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).
Suppose \(h=e\), so \(b=2-a,\ d=a-1,\ h=a/2\). Both fronts choose the
same two of the three free active labels as their new sixth and seventh
clocks. The dormant stage is physical 8 or 10. This precise chart is
impossible over **any characteristic-zero field** given the inherited
tableau premises. The half–half different-extra chart, central dormant
physical 9, and four-distinct calibrations are not excluded here.

## 1. Literal repeated inner pair fixes both remaining clocks

Call the two common extra labels \(t,s\), and the omitted free
label \(u\). The three ordinary crossing pairs are \(h,t,s\).
Both physical occurrences of \(u\) lie in the inner three
positions, together with the genuine dormant nonendpoint
\(\zeta\). For physical dormant 8 the repeated pair is
at 9 and 10. The both-new actual grade-four square-clock
vectors \(V_L,V_R\) have models
\[
 V_a(X)=X^2(X-a)^2,\qquad V_b(X)=(1-X)^2(X-d)^2 .
\]
The literal primitive \(AV_L\) vanishes through physical 8,
and \(V_R\) vanishes from physical 11 onward.
Thus their product only sees rows 9 and 10, both at \(u\).
Testing with and without a clock factor (total grade at most
\(5+4+1=10\)) gives \(C=uH\), where
\[
 J_a(X)=\int_0^X V_a(Y)\,dY,\qquad
 H=\int_0^1 J_a V_b,\qquad C=\int_0^1 X J_a V_b .
\]
The mixed pairing uses the earlier actual low-grade/transpose
bridge, not ordinary reverse order eleven.

Put \(W=V_aV_b\) and \(I_j=\int_0^1 X^j W\).
The actual grade-four product is supported on the inner
three rows. Multiplication by \(C_{\rm clk}-uI\), then
by \(C_{\rm clk}(C_{\rm clk}-uI)\), leaves only the dormant
site. The extra clock budget is two, so their model outputs
are \(I_1-uI_0\) and \(I_2-uI_1\), and the latter is
\(\zeta\) times the former. Define
\[
 M=I_1H-I_0C,\qquad N=I_2H-I_1C .
\]
The exact univariate arithmetic proves
\(\gcd(H,C)=\gcd(M,N)=1\) in \(\mathbb Q[a]\).
Hence \(C=uH\) first implies \(H\ne0\) and \(u=C/H\);
then \(N=\zeta M\) implies \(M\ne0\) and \(\zeta=N/M\).
This is why no ordering is required even for the two
centroid denominators in this specific chart.

## 2. Complete shifted-minor split

Use the *scaled* four-root factor
\[
 P=(X-a)(X-a/2)(X-d)(HX-C),\qquad
 m_j=\int_0^1 X(1-X)P(X)X^j\,dX .
\]
Then the monic active hull is \(P(X)(X^2+q_1X+q_0)/H\).
The nine-site hull, with zero factor \(X(X-1)(X-\zeta)\)
against the active hull, gives exactly the two shifted
equations through test degree one. Write
\[
 e_j=M m_{j+1}-N m_j\ (0\le j\le3),\qquad
 e_0q_0+e_1q_1+e_2=0,\quad e_1q_0+e_2q_1+e_3=0.
\]
This scales the actual two rows by \(HM\), both live.
Use the new shifted minors
\[
 D=e_0e_2-e_1^2,\quad U=e_1e_2-e_0e_3,\quad
 V=e_1e_3-e_2^2 .
\]
The actual equations give \(Dq_1=U,\ Dq_0=V\).
If \(D=0\), both minors \(U,V\) vanish by consistency
regardless of any individual moment \(e_j\). No
unshifted Hankel pivot is presumed. The exact arithmetic
proves \(\gcd(D,U,V)=1\), excluding **all** singular
shifted fibers, including \(e_0=0\).

If \(D\ne0\), the two common free roots have sum \(-U/D\)
and product \(V/D\). Multiply their left/right \(r_0,r_1\)
factors in the derivative contacts by \(D\) to obtain
\[
 L_0=a^2D+aU+V,\quad L_1=-V,\qquad
 R_0=d^2D+dU+V,\quad R_1=-D-U-V.
\]
The actual row-7/row-11 off-diagonal equation is
\[
 Q=L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
                  U_{4,4}(a,b)L_1R_1=0 .
\]
Because the dormant response at 8 vanishes, the actual
anchored left row there is \(D_\zeta/a^5\). Its off-diagonal
pairing with row 11 yields the additional polynomial
\(G=0\), formed as follows. In the left model basis
\(P_i=X^{i+1}\), the entries of \(M^5D_\zeta\) are
\[
 a^5N^{i+1}M^{4-i}
 -a^{i+1}N^3(6N^2-15aNM+10a^2M^2),\qquad 0\le i\le4.
\]
In the right basis \((1-X)X^j\), the entries of the
right derivative row multiplied by \(D\) are
\(R_0+R_1[d^j-bj d^{\,j-1}]\) (take the bracket as 1
at \(j=0\)). Pair these two arrays with the integer inverse
Gram matrix, omitting its common factor 210 since the
pairing is zero. This computes \(G\) using the actual
grade-five primitive that vanishes through physical 8.
No zero pivot of this second contact has been divided out.

The exact calculation gives
\(\gcd(Q,G)=a(a-2)\). The two widths are nonzero, so
\(a\ne0,2\), excluding the nonsingular branch.

## 3. Exact coefficient receipt and physical 10

The modular Lean arithmetic at 101 checks coefficient
interpolation for the nine polynomials \(H,C,M,N,D,U,V,Q,G\)
and their four Bézout identities. The two first degrees are
at most four, \(M,N\) at most eight, and the scaled four-root
factor gives \(\deg_a m_j\le7\). Thus the \(e_j\) have degree
at most 15 and \(D,U,V\) at most 30. The first-contact expression
has degree at most 68. The left cleared array in \(G\) has
entry degrees at most 47 and the right array at most 34,
so \(\deg G\le81\). The grid \(0,\ldots,81\) suffices
for every polynomial. Rational moment denominators and the
factor 30 are units modulo 101.

The leading degrees \(4,8,30,68\) of \(H,M,D,Q\) all
retain their bounds modulo 101. In each gcd test at least
one polynomial retaining its degree ensures a primitive
common factor cannot disappear on reduction. For the
contact test both \(Q\) and \(G\) vanish identically at
\(a=0,2\): at 0 the left contact terms cancel and the
left array is zero; at 2 the reflected width is zero,
the right terms cancel and the right array is zero.
Thus the width factor \(a(a-2)\) already divides both
in characteristic zero, and the degree-preserving modular
Bézout identity leaves no other common factor. The independent
SymPy replay computes the four gcds directly over \(\mathbb Q\).

At physical dormant 10 exchange the forward and reflected
polynomial systems. The repeated \(u\) pair lies in physical
8 and 9, the reverse primitive is zero through its literal
eighth row (physical 10), and the forward low-grade gap
supports the mirrored mixed moments. The model variable
becomes \(Y=1-X\) and the widths exchange. The same proof
uses exactly the common order-eleven mixed pairings available
from the actual order-ten weighted transpose. It does not
assume ordinary reverse order eleven or reflect a proof
that used a forward fifth-grade square.

The [Lean companion](../lean/RKCert/ReviewedNative/ERK11NineSiteHalfSameEdgeGate.lean) checks the finite arithmetic on all four tested versions; the [standalone Python replay](erk11-nine-site-half-same-edge/replay_n12_half_same_edge.py) computes the exact rational coefficient gcds. The rooted transfer remains mathematical.
