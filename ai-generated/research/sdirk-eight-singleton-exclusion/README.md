# The singleton quadratic-zero branch is empty at the ten-stage SDIRK8 floor

A ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field **cannot have exactly one zero** in its quadratic stage residual \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\), where \(\boldsymbol c=A\boldsymbol1\). Strict SDIRK means lower triangular with one common nonzero diagonal \(\gamma\). The proof uses no signs, sorting of clocks, or ordering of the coefficient field. It is independent of the [exactly-two-zero exclusion](../sdirk-eight-two-zero-line/README.md). These exclusions do not decide the unrestricted ten-stage minimum; the real-algebraic interval stays **10–11**.

## 1. The normalized affine graph and its actual reflected graph

Use the genuine grade-\(j\) stage spaces \(E_j,W_j\), with pure spaces \(F_j,Z_j\), and the coordinate matrices \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(B=\operatorname{diag}(\boldsymbol b)\). Let \(U=\ker G\) be the coordinate line of the unique zero stage. The [singleton saturation theorem](../sdirk-eight-saturation/README.md) gives \(E_2\cap U=0\), \(E_3\cap U=U\), clean grade four on this row, and its position \(5\) or \(6\). Its clock \(a\) is a root of the monic shifted \(L_4\), and
\[
             \gamma=\frac{4+35a(1-a)}{72},\qquad
 \Pi_a(X)=\frac{L_4(X)-L_4(a)}{X-a}.
\]
The supported column has normalized scalar trace \(\Pi_a\). Since \(F_3=GE_1\) by the saturation dimension and injectivity of \(G\) on \(E_1\), it has the form \(\Pi_a(\boldsymbol c)+G H(\boldsymbol c)\), \(H\) affine. Thus on every row except the singleton zero row,
\[
         \Pi_a(c_m)=(g_m/g_1)D(c_m),\qquad D=-g_1 H,\quad
         D(\gamma)=\Pi_a(\gamma),\quad g_1=\gamma^2/2.
\]
This equation uses one common affine polynomial \(D\), not a separate slope for every stage.

All weights are nonzero. Indeed the [support-rank identity](../sdirk-eight-two-zero-line/README.md) applies to any size of zero-coordinate space and gives \(W_2\cap U_{\rm row}=0\), since \(\dim U-\dim(E_3\cap U)=0\). Also \(E_3^{\mathsf T}B=W_3\) with injective weighting: the first four ordinary scalar moment probes detect the scalar trace, and \(F_3=\langle\boldsymbol g,C\boldsymbol g\rangle\) is detected at two distinct active nonzero-residual clocks. Such clocks exist since ordinary order requires at least four distinct active clocks and only one row has residual zero. Every silent coordinate would then lie in \(\operatorname{Ann}(W_3)=F_4=GE_2\). But a silent-only vector in \(GE_2\) comes from a weighted row in \(W_2\) supported on \(U\), which is zero. Injectivity of weighting on \(E_2\) implies the vector is zero. Hence there are no silent coordinates.

Let \(A^\star=B^{-1}A^{\mathsf T}B\), with chronology reversed. This **is** an order-eight strict SDIRK tableau in this situation. In the [saturated weighted mirror proof](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md), invertible \(B\) identifies every forward profile with a reverse row of the same scalar density, because \(F_j^{\mathsf T}B=Z_j\). The latter equality follows by pure pairing and equal dimensions. Iterate this identification through actual rooted sums and integration \(J^*\), which is \(J\) in the reflected variable \(1-X\). This proof works over characteristic zero using rational Hilbert rank instead of area or positivity. The physical row sums are \(\boldsymbol1-\boldsymbol c\), since \(Z_1=0\) gives \(D(1)\) exactly.

Write \(\tau=g_s/g_1\ne0\), with \(s=10\). The reflected residual at each physical site is \(\boldsymbol g^\star=\tau^{-1}\boldsymbol g\): the degree-two pure rows \( \boldsymbol b^{\mathsf T}G\) and \(\boldsymbol b^{\mathsf T}M\) are proportional, and their last entries give \(\boldsymbol b^{\mathsf T}G=-(g_s/\gamma^2)\boldsymbol b^{\mathsf T}M\). Apply the reflected commutator \(B^{-1}M^{\mathsf T}B\) to \(\boldsymbol1\). By \(L_4(1-X)=L_4(X)\), \(\Pi_{1-a}(1-X)=-\Pi_a(X)\), so the affine graph on the reflected tableau can be taken to be
\[
                        D^\star(X)=-\tau D(1-X).                 \tag{1}
\]

Use the normalized front variable \(u=(X-\gamma)/\gamma\), so \(D(\gamma(1+u))=p+\ell u\) where \(p=\Pi_a(\gamma)\). Its reflected counterpart \(p'=\Pi_{1-a}(\gamma)=-\Pi_a(1-\gamma)\) is also nonzero. Both nonvanishings are proved by the exact good reduction below (\(p\mapsto15\), \(p'\mapsto10\)); no division by an unknown Gauss value is made. Let \(h=\ell/p\), \(h'=\ell'/p'\), and \(L=1/\gamma-2\). From (1),
\[
     p'=-\tau(p+L\ell),\qquad \ell'=\tau\ell,\qquad
                      h'=-\frac h{1+Lh}.                       \tag{2}
\]
The denominator is necessarily nonzero by \(p'\ne0\), \(p\ne0\), and \(\tau\ne0\). These identities do not assume the tableau is equal to its reflected tableau.

## 2. The first three rows force a cubic in the actual first clock gap

Expand
\[
  P(v)=\Pi_a(\gamma(1+v))=p+d_1v+d_2v^2+d_3v^3,\quad
  \kappa(v)=1+2v-v^2,\quad
  K(v)=d_1-2p+(d_2+p)v+d_3v^2.
\]
Now \(u=(c_2-\gamma)/\gamma\) is the actual gap. It is nonzero by full stage rank (otherwise the first two rows have identical rooted profiles) and \(\kappa(u)\ne0\) because the second row is not the zero stage. From its literal residual and the affine graph,
\[
                            K(u)=p\,\kappa(u)\,h.               \tag{3}
\]

Use the [actual three-row identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md), valid by the same two-coordinate proof over any characteristic-zero field. If \(w=(c_3-\gamma)/\gamma\), the star case has \(w=2-u\), \(w\ne0,u\), and \(g_3/g_1=\kappa(u)=\kappa(w)\). Then \(K(w)=K(u)\) gives
\[
                               d_2+p+2d_3=0 .
\]
The exact reductions below show this scalar nonzero on both the forward and reflected charts, so both use the arithmetic case.

In the arithmetic case \(w=2u\), \(t=A_{32}/\gamma\), and
\[
 tH(u)=2u(3u-2),\qquad H(u)=-2+u+4u^2-u^3,\qquad
 g_3/g_1=\kappa(2u)+2tu.
\]
The third-row graph is \(P(2u)=(\kappa(2u)+2tu)(p+2u\ell)\). Multiply by \(H(u)\kappa(u)\), use the equation for \(tH(u)\) and (3), and subtract to obtain
\[
 H(u)\kappa(u)P(2u)-
  (H(u)\kappa(2u)+4u^2(3u-2))(p\kappa(u)+2uK(u))
                  =2u^2\kappa(u)Q_3(u)=0,
\]
where
\[
\begin{aligned}
Q_3(U)={}&2(d_2+2d_3+p)U^3+(3d_1-4d_2+7d_3-10p)U^2\\
 &+(-8d_1+5d_2-6d_3+15p)U+4d_1-2d_2-6p .
\end{aligned}
\]
The replay checks this identity on the four coefficient columns, which suffices by linearity. Cancelling \(2u^2\kappa(u)\ne0\) gives \(Q_3(u)=0\). This argument does not divide by \(H(u)\). The reflected argument is identical with \(a\) replaced by \(1-a\): its first three physical rows have nonzero quadratic residual and nonzero first gap too.

Define
\[
       F_a(h)=\operatorname{Res}_{U}(Q_3(U),K(U)-p\kappa(U)h).
\]
It is a polynomial of degree at most three in \(h\) (the determinant has three rows of coefficients affine in \(h\)). Equations (2)–(3) would make the two scalar polynomials
\[
        F_a(h),\qquad V_a(h)=(1+Lh)^3 F_{1-a}\!\left(-\frac h{1+Lh}\right)
                                                                  \tag{4}
\]
vanish simultaneously. The latter expression is polynomial despite its displayed form.

## 3. Good reduction proves the two cubics are coprime

The field element \(a\) has minimal polynomial \(L_4\), since with \(Y=2a-1\) the equation is \(35Y^4-30Y^2+3=0\), Eisenstein at 3. Let \(\Lambda=\mathbb Z[1/210,a]\) inside \(\mathbb Q(a)\). The presentation by adjoining a root of the monic \(L_4\) over \(\mathbb Z[1/210]\) is exact: a relation reduces to degree at most three by monic division and irreducibility makes that remainder zero. Both fronts have coefficients in \(\Lambda\); so does \(L\). Indeed \((144\gamma-18)^2=30\) gives \(3456\gamma^2-864\gamma+49=0\), hence \(\gamma^{-1}=(864-3456\gamma)/49\). All denominators in this description are units in the indicated ring.

The assignment \(a\mapsto7\) (and \(1-a\mapsto11\)) in \(\mathbb F_{17}\) is valid since both are actual roots of \(70L_4\) modulo 17 and the inverted integers are nonzero. The replay obtains:

| Front | \(\gamma\) | \(p,d_1,d_2,d_3\) | \(d_2+2d_3+p\) |
|---|---:|---|---:|
| \(a=7\) | 16 | \(15,12,2,16\) | 15 |
| \(1-a=11\) | 16 | \(10,7,6,16\) | 14 |

In particular both \(p\)'s and star coefficients are already nonzero in characteristic zero. The two cubic leading coefficients \(2(d_2+2d_3+p)\) survive, and \(K-p\kappa h\) genuinely has degree two in \(U\) over the polynomial coefficient ring. Its highest coefficient \(d_3+ph\) is not the zero polynomial. Using the fixed Sylvester determinant with the cubic and quadratic degrees, the specialized results are
\[
 \begin{split}
 F_a(h)&=7h^3+6h^2-3h-3,\\
 F_{1-a}(h)&=-4h^3-6h^2+6h+1,\\
 V_a(h)&=-8h^3+6h^2+2h+1\qquad(L=14).
 \end{split}
\]
Thus all three slope polynomials have degree **exactly three** both before and after specialization. In \(\mathbb F_{17}[h]\),
\[
   (-6h^2+7h-6)F_a(h)+(-h^2+3h)V_a(h)=1.
\]
The final \(6\times6\) Sylvester determinant of \((F_a,V_a)\) is \(10\) modulo 17. Since the actual degrees are preserved, that same determinant over \(\Lambda\) is nonzero. Consequently the two polynomials in (4) have no common zero in any extension of \(\mathbb Q(a)\). In particular we did **not** try to reduce the unknown tableau, gaps or slope modulo 17, or assume that any of them has integral reduction. This proves the singleton exclusion over arbitrary characteristic-zero fields without any field ordering or real-closure assumption.

Run [check_resultant.py](check_resultant.py) with Python 3. It is standard-library only: it reproduces the arithmetic factorization from exact integer coefficients, both initial Sylvester determinants, the transformed determinant, the Bézout equation, and the final nonzero residue. All computations concern this conditional singleton chart, not unconditional stage minimality or a positive-characteristic exclusion.

The [native slope receipts](../../lean/RKCert/ReviewedNative/SDIRK8SingletonSlopeReceipts.lean) compile on Lean/Mathlib 4.36.0. They verify the cubic factoring and actual arithmetic-root implication, the 3-by-2 Sylvester common-root identity, the two exact modular jets, the three polynomial congruences, and the Bézout obstruction over any field of characteristic 17. Eight axiom audits report only the ordinary quotient, choice, and propositional extensionality axioms. The tableau reduction, exact presentation of the characteristic-zero coefficient ring, and good-reduction argument are the mathematical proof above rather than one native end-to-end theorem, and no other toolchain is claimed here.
