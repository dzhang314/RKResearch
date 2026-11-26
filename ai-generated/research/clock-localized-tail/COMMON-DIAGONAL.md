# Clock-local causal tails with a nonzero common diagonal

The causal argument for explicit methods also applies when the diagonal of the tableau is a nonzero constant on the interval being tested. Subtracting that constant changes the moments: the longest linear test can vanish, but mixed tests still give a lower bound on the length of the interval. This is a local theorem about actual stages, not a global stage bound or a Lean certificate.

## Result

Let \(A,\mathbf b\) satisfy the Runge–Kutta order conditions through order \(p\), with coefficients in a field in which \(p!\) is nonzero. Suppose \(A\) is lower triangular and has a common diagonal \(\gamma\ne0\) on the physical interval used below. Let \(E_d\) be the span of the original \(\boldsymbol\Phi_t(A)\) for \(|t|\le d+1\). Suppose \(\boldsymbol\eta\in E_d\) is supported at one clock \(\theta\ne1\) and \(\mathbf b\cdot\boldsymbol\eta\ne0\). Define
\[
\mathbf c\coloneqq A\mathbf1,\quad
\delta\coloneqq1-\theta,\quad
\rho\coloneqq\gamma/\delta,\quad
T\coloneqq(A-\gamma I)/\delta,\quad
C\coloneqq\operatorname{diag}\bigl((\mathbf c-\theta\mathbf1)/\delta\bigr).
\]
Choose \(m\ge0\) and \(L\ge4\) with \(d+m+L+1\le p\). Define the normalized output and moments by
\[
\boldsymbol\beta\coloneqq
 \frac{(A^\mathsf T)^m\mathbf b}{((A^\mathsf T)^m\mathbf b)\cdot\boldsymbol\eta},\qquad
\mu_i\coloneqq \frac{m!}{(m+i)!},\qquad
\nu_i\coloneqq\sum_{a=0}^i\binom ia(-\rho)^{i-a}\mu_a
\quad(0\le i\le L).
\]
Let \(\ell\) be the first nonzero stage of \(\boldsymbol\eta\) and \(t_*\) the last nonzero stage of \(\boldsymbol\beta\). The common-diagonal assumption is needed only on \([\ell,t_*]\). Then
\[
t_*-\ell\ge L,\qquad
t_*-\ell\ge L+1\quad\text{if }L\ge6\text{ and }\nu_L\ne0.
\tag{1}
\]
The first assertion holds already for \(L\ge4\). If \(\nu_L\ne0\), a hypothetical saturated suffix of length \(L\) with \(L\ge4\) has last original clock \(1-(m+1)\gamma\). Its penultimate clock cannot equal that value, for the same physical two-dimensional Jordan obstruction as in the explicit case.

In a strict SDIRK method \(\gamma\ne0\) on all stages, so multiplying the output by \(A^m\) does not move its last support: the last nonzero output weight is multiplied by \(\gamma^m\). This is different from the explicit theorem's possible support retreat by \(m\). In a variable-diagonal DIRK, or an ESDIRK with an explicit first row, (1) still applies when the actual observed interval has the required common diagonal. Outside that case it makes no claim.

## The shifted formal action

On the original rooted columns, \(A-\gamma I\) has formal action \(P\mapsto J_0P-\gamma P\), where \(J_0\) is the lower primitive from zero. Under the affine clock change the lower limit becomes \(-\theta/\delta\), not zero. In adjoint tests its normalized action is the upper primitive from the normalized clock to 1 minus \(\rho I\).

Here is the equivalent moment description that will be used. Let \(Z\) be a formal variable and define
\[
\mathcal M(Z^i)\coloneqq\nu_i,\qquad
\mathcal T(P)\coloneqq ZP,\qquad
P_0(Z)\coloneqq(Z+\rho)^2,\qquad
\mathcal C_0(P)\coloneqq P_0P'.
\tag{2}
\]
For every word of cost at most \(L\) in \(T,C\), its actual scalar response on \(\boldsymbol\eta\) equals \(\mathcal M\) applied to the corresponding word in \(\mathcal T,\mathcal C_0\) acting on 1. In particular
\[
\boldsymbol\beta\cdot T^i\boldsymbol\eta=\nu_i.
\tag{3}
\]
For clarity, this uses only a chosen formal linear combination representing \(\boldsymbol\eta\), not uniqueness of an exact profile on the numerical vector. Unary extension and multiplication by a clock give the usual polynomial primitive and clock multiplication on each rooted term. Pairing with \(\mathbf b\) at the indicated cost uses the cleared order equations. Moving the lower primitive to the other side of the polynomial integral gives the upper primitive. Iterating \(A^m\) first pays the adjoint weight \((1-x)^m/m!\) and gives
\[
 ((A^\mathsf T)^m\mathbf b)\cdot\boldsymbol\eta
 =\frac{\delta^m}{m!}\,(\mathbf b\cdot\boldsymbol\eta)\ne0.
\]
With normalized clock \(x\) starting at 0 on the tested support and normalized output as above, the upper primitive \(\mathcal U\) has
\[
(\mathcal U^i(xF))(0)=i(\mathcal U^{i+1}F)(0).
\tag{4}
\]
Indeed for \(i\ge1\) the left side is the integral of \(x^i F(x)/(i-1)!\) from 0 to 1 and the right side is the same; for \(i=0\) both vanish. This is a polynomial integration identity with only paid divisions. Thus before the diagonal shift, if the stage operator is modeled by multiplication by \(Y\), clock multiplication is represented in these scalar responses by \(Y^2\partial_Y\). The scalar for \(Y^i\) is \((\mathcal U^i(1-x)^m)(0)=\mu_i\). Changing variable \(Z=Y-\rho\) proves (2). The assertion includes separated words such as \(T^kCT^hCT^i\), not just adjacent powers of \(C\).

Two elementary consequences of the moments will be useful. First,
\[
 (n+m+1)\nu_{n+1}+\bigl((2n+m+1)\rho-1\bigr)\nu_n+
 n\rho^2\nu_{n-1}=0\qquad(0\le n<L),
\tag{5}
\]
where the last term is omitted at \(n=0\). For a proof, the exponential generating polynomial of \(\mu\) satisfies
\(uM''+(m+1)M'-M=0\) modulo \(u^L\), by \((m+n+1)\mu_{n+1}=\mu_n\). Its shifted counterpart is \(e^{-\rho u}M\) to paid degree \(L\). Substitution gives (5). Only the finite Taylor polynomials through degree \(L\) are used.

Second, for every \(r\) with \(2r-2\le L\), the matrix
\[
 H_{\nu,r}\coloneqq(\nu_{a+b})_{0\le a,b< r}
\]
is invertible. The lower triangular binomial change has diagonal one and takes \(H_{\mu,r}\) to \(H_{\nu,r}\) by congruence. In \(H_{\mu,r}\), multiply row \(a\) by \((m+a+r-1)!/m!\). Column \(b\) then gives the values at \(a=0,\ldots,r-1\) of a monic polynomial of degree \(r-1-b\). These polynomials form a basis and the paid integers distinguish the row arguments, so the matrix is invertible. No positivity or real-root property is required.

## A saturated suffix

All words stay in the actual physical prefix through \(t_*\). On its suffix starting at \(\ell\), \(T\) is strictly triangular. Suppose that this suffix has exactly \(N\) rows after \(\ell\) and that \(\nu_N\ne0\). The nonzero response of \(T^N\boldsymbol\eta\) implies every adjacent edge on the one available maximal path is nonzero. Then \(T^i\boldsymbol\eta\), for \(0\le i\le N\), are a basis with first entries at \(\ell+i\). Use \(Z^i\) for these basis vectors and define
\[
 g(Z)\coloneqq\sum_{a=0}^{N}\frac{\nu_{N-a}}{\nu_N}Z^a,\qquad
 G(Z)\coloneqq 1/g(Z),\qquad
 Q(Z)\coloneqq P_0(Z)-\rho^2G(Z).
\tag{6}
\]
Here \(G\) is a formal power series with a unit constant. All actions on the physical suffix are taken modulo \(Z^{N+1}\). The output on a polynomial vector \(F\) equals \(\nu_N[Z^N](gF)\). The operator \(C\) preserves the successive suffix spaces in this basis, with diagonal entries \(x_i\) equal to the actual normalized clocks.

Suppose first that the pure and mixed tests are paid through degree \(N\). For \(i\ge1\) the one-clock test on \(Z^i\) compares the numerical output with \(iP_0 Z^{i-1}\). All coefficients of \(g\) times the difference in degrees \(i+1,\ldots,N\) vanish. The expression \(iQZ^{i-1}\) is supported from degree \(i\) on, and multiplication by \(g\) changes it from the formal test only by \(-i\rho^2 Z^{i-1}\). The unique leftover term at degree \(i\) is a multiple of \(GZ^i\). Thus the actual clock action is
\[
 \mathcal C(Z^i)=iQZ^{i-1}+\alpha_i GZ^i,\qquad
 q_1\coloneqq[Z]Q,\qquad
 \alpha_i\coloneqq x_i-iq_1 .
\tag{7}
\]
At \(i=0\) this means \(\mathcal C(1)=0\), with \(\alpha_0=0\). If the tests pay one degree further and \(\nu_{N+1}=0\), the comparison also controls degree \(i\); then every (\alpha_i=0\). In that case \(\mathcal C=Q\partial_Z\) on the cyclic suffix. This is a well-defined operator on the truncated polynomial space since \(Q(0)=0\).

## Excluding a loss of one row at resonance

Suppose \(\nu_L=0\). Consecutive moments cannot both vanish: (5) would propagate the pair \(\nu_L=\nu_{L-1}=0\) back to \(\nu_0=0\), using \(\rho\ne0\) and the paid integers. The bare path therefore requires \(L-1\) later rows. If this were exactly the number, set \(N=L-1\). The one-extra-degree conclusion of (7) applies, so \(\mathcal C=Q\partial_Z\). The ideal operator in (2) is \(P_0\partial_Z\). For \(i\ge1\) the difference in their squared actions on \(Z^i\), multiplied by \(g\), is
\[
 i(i-1)Z^{i-2}(-2\rho^2P_0+\rho^4G)
 +i Z^{i-1}(-\rho^2P_0'-\rho^2QG'/G).
\tag{8}
\]
The first term is omitted when \(i=1\). The two-clock words read the coefficients from degree \(i+1\) through \(N\); indeed \(i+2+k\le N+1\). The degree-2 and degree-1 pieces \(P_0,P_0'\) in (8) are therefore invisible. Tests at \(i=1\) give \([Z^a](QG'/G)=0\) for \(2\le a\le N\). At \(i=2\), the same vanishing yields \([Z^a]G=0\) for \(3\le a\le N\).

Let \(G_*\) be the degree-at-most-two truncation of \(G\), and set \(Q_*\coloneqq P_0-\rho^2G_*\). Since \(Q_*(0)=0\), the congruence for \(QG'/G\) gives an equality
\[
 Q_*G_*'=\lambda ZG_*
\]
for some scalar \(\lambda\): both sides have degree at most three, and \(N\ge3\). In a splitting field, any root \(r\) of \(G_*\) has multiplicity one or two, hence its derivative has multiplicity one less. Divisibility by \(G_*\) implies \(Q_*(r)=0\), so \((r+\rho)^2=0\). Thus
\[
G_*=(1+Z/\rho)^e,\qquad e\in\{0,1,2\}.
\]
If \(e=0\), (6) gives \(\nu_0=0\). If \(e=1\), the reversed list of \(\nu_i\) is geometric with forward ratio \(-\rho\), whose inverse binomial translation gives \(\mu_1=0\). If \(e=2\), one has \(\nu_i=D(-\rho)^i(N-i+1)\) for a nonzero constant \(D\) and \(0\le i\le N\). Inverse binomial translation gives \(\mu_2=0\), since a second finite difference of an affine polynomial vanishes. All contradict the paid moments. Hence at least \(L\) later rows are required, including at resonance.

## Excluding saturation when the top moment is nonzero

Suppose \(\nu_L\ne0\). The bare path requires \(L\) later rows. If this were exact, set \(N=L\) and use (7). Write \(g_1\coloneqq[Z]g\) and define
\[
 a_0\coloneqq (2N+m+1)\rho-1,\qquad
 h_0\coloneqq a_0+N\rho^2 g_1,\qquad
 R\coloneqq QG'/G,\qquad
 G_d\coloneqq[Z^d]G .
\]
The reversed recurrence (5) gives
\[
 P_0g'\equiv
 \bigl((m+N)Z+a_0\bigr)g+(N+1)\rho^2(g-1)/Z-h_0
 \pmod{Z^{N+1}}.
\]
At constant coefficient this is the definition of \(h_0\). At coefficient \(d\ge1\) it is (5) for \(n=N-d\). Multiplying by \(-G\) and using \(G'/G=-g'/g\) gives, for \(2\le d\le N\),
\[
 [Z^d]R=(N-d)\rho^2 G_{d+1}+h_0G_d.
\tag{9}
\]
Any formal \(G_{N+1}\) is multiplied by zero here.

Consider the actual separated reads \(T^kCT^hCT\boldsymbol\eta\) at total cost \(k+h+3\le N\). Set \(j\coloneqq N-k\), \(d\coloneqq j-1-h\), and
\[
 F_{j,d}\coloneqq(h_0+\alpha_j)G_d+(N-j)\rho^2 G_{d+1}.
\]
The exact resulting relation is
\[
                 \alpha_1F_{j,d}=\rho^2 F_{j,d+1}
                 \qquad(2\le d\le j-1).
\tag{10}
\]
Here are the terms that give (10). In the polynomial representation, the input to the second clock operation is \(Z^h(Q+\alpha_1 GZ)\), whereas its formal counterpart is \(Z^hP_0\). Apply the actual operator (7), the formal operator (2), and multiply the difference by \(g\). At coefficient \(j\) the terms are
\[
 h\rho^4G_{d+2}-\rho^2 R_{d+1}+\alpha_1 R_d
  +\bigl(\alpha_1(h+1)+\alpha_j\bigr) Q_{d+1}
  +\alpha_1\alpha_jG_d ,
\]
where \(R_a=[Z^a]R\) and \(Q_a=[Z^a]Q\). This follows by expanding the derivative: in the term with \(hZ^{h-1}\), \(g(Q^2-P_0^2)=-2\rho^2P_0+\rho^4G\), and in the term with \(Z^h\), \(g(QQ'-P_0P_0')=-\rho^2P_0'-\rho^2R\). The degree-2 and degree-1 contributions lie below \(j\). Using \(Q_{d+1}=-\rho^2G_{d+1}\) and (9), the displayed coefficient is \(\alpha_1F_{j,d}-\rho^2 F_{j,d+1}\). The paid word makes it zero. The case \(h=0\) simply omits the first term.

Now choose \(j=N-1\) and put
\[
 a\coloneqq\alpha_1/\rho^2,\qquad
 b_0\coloneqq(h_0+\alpha_{N-1})/\rho^2 .
\]
For \(2\le d\le N-2\), (10) gives
\[
G_{d+2}+(b_0-a)G_{d+1}-ab_0G_d=0.
\]
Consequently \(P\coloneqq(1-aZ)(1+b_0Z)G\) has degree at most three through degree \(N\), and has constant one. Let \(P_*\) be its degree-three truncation. Then
\[
gP_*\equiv(1-aZ)(1+b_0Z)\pmod{Z^{N+1}}.
\]
The coefficients from degree 3 through \(N\) give the reversed relation
\[
\nu_n+P_{*,1}\nu_{n+1}+P_{*,2}\nu_{n+2}+P_{*,3}\nu_{n+3}=0
\qquad(0\le n\le N-3),
\]
where \(P_{*,i}\coloneqq[Z^i]P_*\). If \(N\ge6\) this is a nonzero kernel vector for \(H_{\nu,4}\). Invertibility proved above is a contradiction. Saturation is impossible.

## The shifted endpoint and the old Jordan block

In the same hypothetical saturated nonresonant chart, take \(j=N\) in (10). If \(h_0+\alpha_N\ne0\) then the coefficients of \(G\) from degrees 2 through \(N\) are geometric. Multiplying by \(1-aZ\) makes the result degree at most two through degree \(N\). Reversing the resulting relation on \(g\) puts a nonzero vector in the kernel of \(H_{\nu,3}\) as soon as \(N\ge4\). Thus \(h_0+\alpha_N=0\), or
\[
 x_N=1-(m+1)\rho.
\]
Write \(x_*\coloneqq1-(m+1)\rho\). If \(x_{N-1}=x_*\) as well, the coefficient of \(Z^N\) in \(\mathcal C(Z^{N-1})\) is
\[
 (N-1)(1+2\rho g_1+\rho^2g_2)-x_*g_1=-(m+1),
 \qquad g_2\coloneqq[Z^2]g .
\]
The equality is (5) at \(n=N-1\) divided by \(\nu_N\). The last two physical rows would give a nonscalar two-dimensional invariant block of \(C\) with one eigenvalue, impossible for a diagonal operator. The original clock value of that endpoint is \(1-(m+1)\gamma\).

There is no unconditional \(L+1\) assertion at a zero of \(\nu_L\), and the nonresonant \(L+1\) proof uses the full separated two-clock words and \(L\ge6\). In particular it is not a claim about only the adjacent-word hypotheses of the previous abstract ERK theorem. The exceptional scalar parameter is real: for every odd \(L\), \(\nu_L(0)>0\) and the leading coefficient in \(\rho\) is negative, so there is a positive real zero. This is an obstruction to the bare shifted path argument, not an example of a real RK tableau with a saturated exceptional suffix.
