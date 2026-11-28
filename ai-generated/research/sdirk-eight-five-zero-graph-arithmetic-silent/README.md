# Five zero rows, arithmetic front and silent physical eighth

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) with common diagonal \(\gamma\ne0\), of ordinary order at least eight over a characteristic-zero field. Let \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), \(C=\operatorname{diag}\mathbf c\), \(G=\operatorname{diag}\mathbf g\), and \(U=\ker G\). Assume exactly five physical entries \(g_i=0\), a genuine quadratic graph as the degree-two supported direction, no nonzero output weights on the off-zero rows, first physical zero at row 4 with the initial three off-zero rows in the literal arithmetic phase, and physical row 8 silent.

**Result.** This conditional chart is impossible over any characteristic-zero field. The proof does not use an ordering or a real embedding. It includes both regular and singular graph pencils and all six orders of the three early zero clocks. It does not address the live-eighth arithmetic case.

## 1. Literal clock data and the ordinary cubic

By the [support census](../sdirk-eight-five-zero-support-rank/README.md), the [no-four-site graph theorem](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md) and the [distinct-off result](../sdirk-eight-five-zero-graph-distinct-off/README.md), all five zero rows are live at distinct clocks and all five off-zero clocks are distinct. As in the [first-zero-three silent-rear packet](../sdirk-eight-five-zero-graph-third-silent-eighth/README.md), the weighted reverse multiplier is nonzero on the fifth, silent off-zero row at physical 8, so the literal rear gate gives
\[
 t=c_9=1-\gamma(1+v),\quad s=c_{10}=1-\gamma,\qquad
 v^3-4v^2-v+2=0.
\]
There are three early zero rows before row 8. Their exact interleaving with other off-zero rows is immaterial to the supported reads.

Mask the two known live clocks with \((T-t)(T-s)\). Let \(I(T^j)=1/(j+1)\) and
\[
 m_j=I(T^j(T-t)(T-s))=\frac1{j+3}-\frac{t+s}{j+2}+\frac{ts}{j+1}\quad(0\le j\le5).
\]
The [ordinary Hankel lemma](../sdirk-eight-ordinary-hankel-pivot/README.md) gives
\(\Delta=\det(m_{i+j})_{i,j=0}^2\ne0\) from five distinct live sites. Its Cramer numerators \(q,\ell,k\), in that order, solve the recurrence for the monic cubic on the early zeros against right side \((-m_3,-m_4,-m_5)\). Consequently their **scaled** clocks, denoted \(a,b,c\) in physical order, are the three roots of
\[
 Q_A(X)=X^3+kX^2+\ell\Delta X+q\Delta^2 .
\]
Given a root \(a\), the second root \(b\) satisfies
\(b^2+(a+k)b+a^2+ka+\ell\Delta=0\). The third is \(c=-k-a-b\). The discriminant is nonzero. The quadratic-over-cubic algebra on \(a,b\) is free of rank six; its six components at the actual diagonal are exactly all orders of the three distinct early roots.

We need the additional **global ordinary guard**: none of the five distinct live clocks is a root of \(L_4(X)=70X^4-140X^3+90X^2-20X+1\). Its first four ordinary moments vanish by the degree-seven rule. If some scalar \(L_4(c_i)\) vanished, the other four entries of \((b_iL_4(c_i))_i\) would lie in the kernel of a square Vandermonde, hence vanish, contradicting five distinct roots of a nonzero quartic. This also proves that the norm of the first early \(L_4\) evaluation is nonzero, not just the evaluation at the chosen physical first zero.

## 2. Three supported equations in the same arithmetic pencil

Normalize the graph by \(\mathbf x=\mathbf c/\gamma\), \(\boldsymbol\eta=\mathbf g/\gamma^2\). Its first three off-zero reads pin [the literal arithmetic interpolation](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md):
\[
 P(T)=2T-1-T^2/2+\lambda(T-1)(T-1-u),\qquad
 \lambda(-2+u+4u^2-u^3)=3u-2.
\]
The physical supported column is \(P(\mathbf x)-\boldsymbol\eta\). In the scaled clocks of the cubic, put \(d=\Delta\), \(g=\gamma\Delta\), and use \(\widehat P(T)=g^2P(T/g)=P_0+\beta R_1+\alpha R_2\), where
\[
 P_0=-g^2+2gT-T^2/2,\quad
 R_1=g(T-g),\quad R_2=(T-g)^2,\quad
 \alpha=\lambda,\quad\beta=-u\lambda .
\]
The actual rescaled matrix is \(\Delta A\), with diagonal \(g\). Write \(J\) for the polynomial primitive from zero, and \(L_3,L_4\) for the third and fourth shifted Legendre polynomials scaled to the endpoint \(d\).

The grade-three supported read on the zero rows is clean, by \(F_3=GE_1\). The grade-four \(T\widehat P\) discrepancy is in the line of \(L_4\); the grade-five \(T^2\widehat P\) discrepancy is in the span of \(L_3,L_4\). These are the [actual supported grade and moment gates](../sdirk-eight-five-zero-graph-third-live-eighth/README.md) with diagonal \(1\) replaced by the rescaled diagonal \(g\). They can also be seen from ordinary moment tests of degrees \(3\) and \(2\) respectively on the five distinct live sites.

For any trial polynomial \(P\) in this pencil, the first zero gives
\(F(P)=JP(a)-gP(a)=0\). Put \(\eta=g\,aP(a)-J(TP)(a)\), so the grade-four coefficient is \(\eta/L_4(a)\). The second-zero equation after eliminating its single earlier supported tap is
\[
 G(P)=L_4(a)[a(JP(b)-gP(b))+g bP(b)-J(TP)(b)]-L_4(b)\eta=0 .
\]
At the first three zeros the grade-five discrepancy values are
\[
\begin{aligned}
d_a&=g a^2P(a)-J(T^2P)(a),\\
d_b&=g b^2P(b)+a^2(JP(b)-gP(b))-J(T^2P)(b),\\
d_c&=g c^2P(c)+(a+b)[J(TP)(c)+\eta L_4(c)/L_4(a)-g cP(c)]\\
   &\qquad-ab[JP(c)-gP(c)]-J(T^2P)(c).
\end{aligned}
\]
The last line follows from \(a^2p+b^2q=(a+b)(ap+bq)-ab(p+q)\) for the two earlier actual supported taps. Let \(H(P)\) be \(L_4(a)\) times the determinant of the three columns of \(L_3,L_4,(d_a,d_b,d_c)\). It must vanish. This construction needs no inverse of a tap, a zero-stage graph value or a graph-pencil coefficient.

Write \(F_i,G_i,H_i\) for the corresponding values on \(P_0,R_1,R_2\), respectively. Define
\[
 D_0=F_1G_2-F_2G_1,\quad B_N=F_2G_0-F_0G_2,\quad A_N=F_0G_1-F_1G_0 .
\]
Then \(A_N=\alpha D_0\), \(B_N=\beta D_0\). The regular case requires
\[
 X=D_0H_0+B_NH_1+A_NH_2=0,\qquad
 Y=-2A_N^3-B_NA_N^2+4B_N^2 A_N+B_N^3+(3B_N A_N+2A_N^2)D_0=0.
\]
The second identity clears the literal arithmetic relation without dividing by \(u\), \(\lambda\) or \(D_0\). The singular case \(D_0=0\) requires \(A_N=B_N=0\).

## 3. Exact norm gcds with only admissible guards

Work in \(K=\mathbb Q[v]/(v^3-4v^2-v+2)\), a field since the cubic is already irreducible mod 19. It is enough to work at the formal root \(v\), since each root in any characteristic-zero field defines such an embedding. The replay forms the polynomials in \(\gamma\) over \(K\) by exact rational arithmetic, using the rank-six quadratic-over-cubic algebra above. The norms of \(X,Y\) have degrees 654,954; those of \(D_0,A_N,B_N\) have degrees 348,348,342. All exact content divisions in constructing these inputs use factors of \(\gamma\) and \(\Delta\) only.

Set \(D=\operatorname{Disc}(Q_A)/\Delta^2\) and \(L=N(L_4(a))/\Delta^{16}\). The degree-six \(\Delta\), degree-24 \(D\), and degree-48 \(L\) are all nonzero at any actual diagonal, by distinctness, the structural ordinary pivot, and the non-Gaussian guard for **all** roots. They are constructed by exact polynomial divisions, not trial quotienting.

The replay checks that \(\Delta^{48}D^3L^3\) divides both regular norms exactly. It also checks that \(\Delta^{30}DL\) divides all three singular norms exactly. These common divisors have degrees 504 and 252. The exact polynomials and divisors have degree-preserving reductions over \(\mathbb F_{19^3}\). The residue gcds for the regular pair and the singular pair \(N(D_0),N(A_N)\) are the displayed divisors up to a unit. The unused third singular norm also has the asserted exact divisor. In characteristic zero, the common gcd can have no larger degree: for a fixed pair the gcd degree is the nullity of its Sylvester matrix, and reduction can only lower rank when the polynomial degrees are preserved. Thus the exact common divisors exhaust the characteristic-zero possibilities, and there is no actual root.

Run `python check_guarded_norms.py` with Python-flint 0.8. The replay is independently executable in about ten seconds. All norms use multiplication matrices over exact polynomial rings; the mod-19 test is a characteristic-zero rank certificate with exact common divisors, not a prime-field search. This note and its exact Python replay do not claim a Lean verification of the arithmetic exclusion.

The [Lean graph-pencil module](../../lean/RKCert/Research/SDIRKEightFiveZeroGraphArithmeticFront.lean)
checks the Cramer numerators, the third supported read, the arithmetic
eliminant, and the singular-pencil case over an arbitrary commutative
ring, without dividing by the pencil determinant. Checked in Lean
4.36.0 with only standard axioms. The norms and the bridge from
tableau data to these scalar hypotheses remain outside this module.
