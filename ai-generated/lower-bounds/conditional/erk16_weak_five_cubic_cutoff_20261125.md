# Elementary cubic exclusion for the weak-five twelve-moment chart

This is a source proof over an ordered field. It uses the actual six local and six global tests, a polynomial integration-by-parts identity, and two universal Jacobi sign evaluations. There is no determinant, resultant, fixed-fibre calculation, real closure, or Lean claim. It closes degree three only; degree four remains open.

Put \(v=1-z\), \(w=x(1-x)\), and let the distinct chronological marks be \(0,u,a,h,z\), all different from \(1\). Let \(q\) be monic cubic, \(q^\star(x)=-q(1-x)\), and
\[
N=(X-u)(X-z)(X-a)(X-h),\qquad M=qN.
\]
The checked weak-five moments give
\[
\int_0^u x^j q(x)\,dx=\int_0^v x^j q^\star(x)\,dx=0\quad(j=1,2),\qquad
\int_0^1 wMR=0\quad(\deg R\le5),
\]
and the two true anchored zeros
\[
F(a)=G(h)=0,\qquad
F(Y)=\int_0^Y x(x-u)q(x)\,dx,\qquad
G(Y)=\int_Y^1(1-x)(z-x)q(x)\,dx.
\]
The reflection of this scalar setup swaps the outer lengths and the two inner marks: \(q,u,a,h,z\) are replaced by \(q^\star,v,1-h,1-a,1-u\). The two end pairs swap. With the new \(F,G,M\) denoted by tildes, substitution gives \(\widetilde F(1-h)=-G(h)\), \(\widetilde G(1-a)=-F(a)\), and \(\widetilde M(x)=-M(1-x)\), so all the stated tests are preserved. Distinctness and exclusion of \(0,1\) on non-origin marks are preserved as well. The proof uses no nonvanishing at the reflected origin.

## 1. End lengths and the reflection mismatch

We first obtain \(u,v>0\) and \(s=u+v>1\). The argument uses only the finite positive exact rule, affinely placed on the stated intervals. If all degree-at-most-\(k\) tests vanish against a nonnegative weight times a polynomial, and some weighted sample is nonzero, then there are at least \(k+1\) sign changes among its nonzero weighted samples. Otherwise a product of the linear separators between successive opposite-sign runs gives a test of degree at most \(k\) with every sample of the same sign and at least one strict sample. Conversely a degree-\(m\) polynomial has at most \(m\) sign changes on any increasing list of samples: \(m+2\) alternating nonzero values would make the degree-\((m+1)\) Lagrange interpolation coefficient a sum of nonzero terms of one sign. These statements do not require roots to exist in the ordered field.

If \(u<0\), the left end pair produces two changes on \((u,0)\), with positive weight \(-x\). Use the global tests \(R=(N/(X-u))S\), \(\deg S\le2\), to produce three changes on \((0,1)\), with nonnegative weight \(w(X-u)(N/(X-u))^2\). The weighted samples are not all zero: on the open interval the weight vanishes only at the three remaining marks, and \(q\) has degree three. All integrands have degree at most fourteen. Combining the two sample lists contradicts cubic degree. Reflect for \(v<0\); neither endpoint is zero. If \(s\le1\), the two end windows \((0,u)\), \((z,1)\) are disjoint and each supplies two changes, again a contradiction. Hence \(s>1\). We can now reflect if needed and use \(d=u-v\ge0\).

Write \(q=X^3+bX^2+cX+e\) and \(C_2=b+3/2\), \(C_0=q(1/2)\). The two left end equations divided by the appropriate powers of \(u\) give
\[
c=-\frac65(u^2+bu),\qquad e=\frac25u^3+\frac3{10}bu^2.
\]
Apply them also to \(q^\star\), whose quadratic coefficient is \(-3-b\), whose linear coefficient is \(3+2b+c\), and whose constant at the midpoint is \(-C_0\). Substitution yields
\[
(10-6s)C_2=(6s-9)d,\quad
20C_0=f(u)+C_2g(u),\quad -20C_0=f(v)-C_2g(v),
\]
where \(f(x)=(x-1)^2(8x-5)\) and \(g(x)=5-12x+6x^2\).

If \(d=0\), adding the last two equations gives \(f(u)=0\). As \(u\ne1\), \(u=v=5/8\), \(s=5/4\), and the first equation gives \(C_2=0\). If \(d>0\), write \(r=5-3s\); the first equation excludes \(r=0\) and gives \(C_2=d/(2r)-d\). The sum of the last two equations, using
\[
f(u)+f(v)=\tfrac12(s-2)^2(4s-5)+(6s-\tfrac{21}{2})d^2,\qquad
g(u)-g(v)=6(s-2)d,
\]
becomes
\[
d^2=\frac{(5-3s)(s-2)^2(4s-5)}{3(s-1)}.
\]
Since \(s>1\), strict positivity gives \(5/4<s<5/3\), \(0<r<5/4\). Thus in both cases
\[
s\ge5/4,\qquad C_2\ge-3d/5.
\]

Here is a uniform cutoff \(u,v<11/12\). The equal-length case already has it. For \(d>0\),
\[
\frac{d^2}{(2-s)^2}=\frac{r(5-4r)}{3(2-r)}.
\]
- If \(s\le3/2\), the ratio is less than \(4/9\), because \((4/3)(s-1)-(5-3s)(4s-5)=(36s^2-101s+71)/3>0\). In fact \(36s^2-101s+71=36(s-101/72)^2+23/144\). Hence \(u,v<(s+4)/6\le11/12\).
- If \(3/2\le s\le19/12\), then \(r\le1/2\); \(r(5-4r)\le3/2\) since \(3/2-r(5-4r)=(1/2-r)(3-4r)\). The ratio is at most \(1/3<9/25\), so \(u,v<3/5+s/5\le11/12\).
- If \(19/12\le s<5/3\), then \(r\le1/4\) and the ratio is at most \(5/21<1/4\). Hence \(u,v<1/2+s/4<11/12\).

In particular \(0<z<u<11/12\), since \(v<1\) and \(s>1\).

## 2. The anchored paid mean and a root-free cutoff

Set \(L=X(X-u)\). The values \(F(0)=F(u)=0\) (the latter is the end-pair combination) and \(F'=Lq\) give
\[
F=\tfrac16 L^2 H,\qquad H=X^2-SX+P
\]
with \(H\) monic. The following is the portable observation: \(F/(X-u)\) is a polynomial vanishing at both \(0,u\), and
\[
(F/(X-u))'=Xq-\tfrac16 X^2H.
\]
The independent first end test therefore pays \(\int_0^u x^2H=0\). This mean identity is not limited to cubics, with the corresponding harmless normalization of the quotient. Here it gives
\[
P=\tfrac34uS-\tfrac35u^2,\qquad
H=(X-\mu)(X-(S-\mu))-\tfrac3{80}u^2,\qquad \mu=\tfrac34u.
\]
In particular if an actual port \(a\) and its exact companion \(A\) factor \(H\), then \((a-\mu)(A-\mu)=-3u^2/80\). This yields strict straddling over the base field; no root extraction is required.

Differentiating the factorization gives \(q=(2L'H+LH')/6\). Its quadratic coefficient is \(b=-(5S+4u)/6\), so \(S-\mu=9/5-(6/5)C_2-(31/20)u\). The previous lower bound on \(C_2\), \(d=2u-s\), and \(s\ge5/4\) imply
\[
S-\mu \ \le\ \tfrac95+\tfrac{18}{25}d-\tfrac{31}{20}u
=\tfrac95-\tfrac{18}{25}s-\tfrac{11}{100}u
\ \le\ \tfrac9{10}-\tfrac{11}{100}u.
\]
Let \(B=14/15\). Since \(B-\mu>0\),
\[
H(B)\ge (B-\tfrac34u)(B-\tfrac9{10}+\tfrac{11}{100}u)-\tfrac3{80}u^2.
\]
The right side is a concave quadratic in \(u\), its quadratic coefficient \(-3/25\). Its endpoint values at \(0,11/12\) are \(7/225,53/36000\), both strictly positive. The quadratic lies above the affine chord, so the bound is strictly positive. Both \(\mu\) and \(S-\mu\) are less than \(B\). Therefore for \(x\ge B\), \(H'(x)=2x-S>0\) and \(H(x)-H(B)=(x-B)(x+B-S)\ge0\). Also \(L(x),L'(x)>0\) there. It follows directly that
\[
F(x)>0,\qquad q(x)>0\qquad (x\ge B).
\]

The actual two anchored ports now do different necessary jobs. First \(F(a)=0\) forces \(a<B\). Second, \(G(h)=0\) forces \(h<B\): if \(B\le h<1\), the integrand of \(G(h)\) is strictly negative on \((h,1)\) because \(x>z\) and \(q(x)>0\). If \(h>1\), its integrand is strictly positive on \((1,h)\), but the signed orientation in \(G(h)\) makes the integral negative again. The remaining case \(h=1\) is forbidden. Strict integration signs follow from the positive affine exact rule, with integrand of degree five. Thus all four marks are less than \(B\), and
\[
M(x)=q(x)N(x)>0\quad\hbox{for all }x\ge B.
\]

## 3. Two universal signs obstruct the cubic Jacobi pencil

Let \(J_n\) be monic for the weight \(w\) on the unit interval. To construct the two required polynomials, put \(y=2x-1\) and
\[
P_n(y)=\frac{1}{2^n n!}D^n(y^2-1)^n.
\]
Integrating by parts \(n\) times shows \(P_n\) is orthogonal to all lower degrees for unit weight on \([-1,1]\). Boundary terms vanish because the derivatives of orders \(0,\ldots,n-1\) of \((y^2-1)^n\) vanish at both endpoints. Then \(P'_{n+1}\) is orthogonal to degrees at most \(n-1\) for weight \(1-y^2\): integrating against \((1-y^2)R\) by parts leaves \(P_{n+1}\) against a polynomial of degree at most \(n\). Expansion and monic normalization in \(x\) give exactly
\[
J_6(x)=\frac{429y^6-495y^4+135y^2-5}{429\cdot 2^6},\qquad
J_7(x)=\frac{y(715y^6-1001y^4+385y^2-35)}{715\cdot 2^7}.
\]
Any monic degree-seven polynomial orthogonal to degrees at most five is \(J_7+\alpha J_6\): subtract to cancel the top two coefficients, then test the remaining degree-at-most-five polynomial against itself. Its \(w\)-weighted square has degree at most twelve and is strictly positive on some interior grid sample unless the polynomial is zero. Thus \(M\) has this form. This is a consequence of the cubic degree and six global tests, not from the positive cutoff.

At \(x=B=14/15\) and \(x=15/16\), the values of \(y\) are \(13/15,7/8\). For either point the bracket denominator is the sixth power of the positive denominator of \(y\), and the extra factor \(y\) for \(J_7\) is positive. The sign numerators, directly by Horner substitution, are
\[
\begin{array}{c|rr}
y & J_6\text{ sign numerator} & J_7\text{ bracket numerator}\\ \hline
13/15 & -12224064 & -86239040\\
7/8 & 192061 & -1602629
\end{array}
\]
If \(\alpha\ge0\), \(M(14/15)<0\). If \(\alpha<0\), \(M(15/16)<0\). Both contradict the positivity forced by the two actual anchors. There is no polynomial-root location premise and no root existence theorem in this argument. The earlier assertions that the physical knots lie below the cutoff were proved directly from signed primitives, not inferred from the Jacobi pencil. Consequently this excludes every cubic profile in the actual weak-five scalar packet. The degree-four proof would require a different bound.

The transferable step is the paid mean of the double-anchor quotient. For any monic \(q\) of degree \(m\ge1\) the quotient in \(F=X^2(X-u)^2H/(m+3)\) has degree \(m-1\), with \(\int_0^u x^2H=0\). For degree four the quotient is cubic; neither our special quadratic estimate nor the two-column Jacobi pencil transfers as stated.

The [rational replay](check_erk16_weak_five_cubic_cutoff_20261125.py) independently reconstructs the two Jacobi polynomials, checks their moments and the four signs, and verifies the cutoff constants. It does not check any tableau or replace the signed-interval argument.
