# The common-diagonal scalar cap cannot be attained at nonlinear order p >= 5

This gives the local mixed-fork derivation of the [common-diagonal bound](../../lower-bounds/characteristic-zero/sdirk-common-diagonal-nonlinear-cap.md). No stability, signs, sparsity
pattern beyond triangularity, or ordered coefficient field is assumed.

**Theorem.** Over any field of characteristic zero, let a triangular RK
tableau have actual common diagonal \(\gamma\), including zero, and \(s\)
physical stages. If it satisfies all rooted-tree order conditions through
\(p\ge5\), then \(s\ge p\). If \(\gamma=0\), this is the ordinary tall-tree
bound. For nonzero \(\gamma\), the argument excludes equality in the
scalar cap \(p\le s+1\) whenever \(s\ge4\).

This improves the tall-only common-diagonal threshold by one at all
orders in the stated range. It does not concern differing-diagonal
DIRK, A-stability, L-stability, restricted Pade stability approximants, or
attainment at \(s=p\).

## 1. Scalar cap and saturation of actual support

Let \(e=1\), \(B=A-\gamma I\), \(c=Ae\), and write stage-variable products
componentwise. The rooted convention is
\(\Phi(\bullet)=e\) and
\(\Phi([u_1,\ldots,u_k])=\prod_j A\Phi(u_j)\).
Use tree factorial
\(\rho(\bullet)=1\),
\(\rho([u_1,\ldots,u_k])=|[u_1,\ldots,u_k]|\prod_j\rho(u_j)\);
the required output is \(b^T\Phi(u)=1/\rho(u)\).

For all paid \(n+1\le p\), the tall conditions give
\[
 b^TB^ne=\lambda_n,\qquad
 \lambda_n=\sum_{j=0}^n\binom nj\frac{(-\gamma)^{n-j}}{(j+1)!}.
\]
Use the right side to define all \(\lambda_n\) even when unpaid. The formal
generating function for \(\Lambda(z)=\sum_{n\ge0}\lambda_nz^n\) satisfies
\[
 z\Lambda(z)=\exp\!\left(\frac{z}{1+\gamma z}\right)-1,\qquad
 (1+\gamma z)^2(z\Lambda)'=1+z\Lambda.
\]
Indeed, sum the binomial expansion first over \(n-j\), then over \(j\).
Thus \(\lambda_0=1\) and
\[
 (n+2)\lambda_{n+1}
   =(1-2(n+1)\gamma)\lambda_n-n\gamma^2\lambda_{n-1}
       \qquad(n\ge1).
 \tag{1}
\]
As \(B^s=0\), at \(p\ge s+2\) the consecutive paid values
\(\lambda_s,\lambda_{s+1}\) vanish. For \(\gamma\ne0\), (1) descends
to \(\lambda_0=0\), impossible. For \(\gamma=0\) even the first of these
vanishings contradicts \(\lambda_s=1/(s+1)!\), giving \(s\ge p\).

It remains to consider \(p=s+1\), \(\gamma\ne0\), \(s\ge4\).
Then
\[
                 \lambda_s=0,\qquad L:=\lambda_{s-1}\ne0.
 \tag{2}
\]
Nonvanishing follows from (1) just as above. Because
\(b^TB^{s-1}e=b_s\prod_{i=2}^s B_{i,i-1}=L\ne0\), every displayed
physical subdiagonal entry and \(b_s\) is nonzero. In particular this
is not a claim about a fictitious cyclic realization. For
\(w_h=b^TB^h\), strict chronology gives
\[
                  \operatorname{supp} w_h\subseteq\{1,\ldots,s-h\}.
 \tag{3}
\]
The new nonlinear tests will see only two or three actual physical
rows near this scalar saturation.

## 2. Exactly paid nonlinear tests

A bush with \(m\) leaves has stage value \(c^m\), order \(m+1\), and
factorial \(m+1\); adding \(k\) unary ancestors gives output
\(m!/(k+m+1)!\). The mixed fork \([\bullet,[\bullet]]\) has stage value
\(c(Ac)\), order four, and factorial eight; adding \(k\) unary ancestors
gives \(3/(k+4)!\). Expanding \(B^h\) as a polynomial in \(A\) pays
only the trees through the displayed maximal orders. Thus
\[
 w_h c^m=m!\,w_h A^m e \quad(h+m+1\le p),\qquad
 w_h\big(c(Ac)\big)=3w_h A^3e \quad(h+4\le p).
 \tag{4}
\]
Only \(m=2,3\) and the one mixed fork are needed beyond tall conditions;
the expansions include their relevant unary extensions.

Set \(x=c-\gamma e=Be\), \(a=x_2=B_{21}\), and \(d=x_3\). Thus
\(x_1=0\), \(a\ne0\), and \((Bx)_1=(Bx)_2=0\).
For an eligible \(h\), write \(M_j=w_h x^j\). From (4) and the binomial
expansion:
\[
\begin{aligned}
 M_1 &=\lambda_{h+1},\\
 M_2 &=\gamma^2\lambda_h+2\gamma\lambda_{h+1}+2\lambda_{h+2},\\
 M_3 &=2\gamma^3\lambda_h+9\gamma^2\lambda_{h+1}
             +12\gamma\lambda_{h+2}+6\lambda_{h+3}.
\end{aligned}
\tag{5}
\]
For \(h=s-2\), \(M_2\) is paid at order \(s+1\) and only the first two
rows contribute, so \(M_2=a M_1\). Equations (1) and (2) give
\[
      a=2\gamma+\frac{\gamma^2\lambda_{s-2}}{L}
        =\frac{1-2\gamma}{s-1}.
 \tag{6}
\]

For \(h=s-3\), \(M_3\) and the mixed fork are both paid at order \(s+1\).
Now \(w_h Bx=L\) and \(w_h(x\,Bx)=dL\), since only the first three
coordinates contribute. Expand
\[
   Ac=\gamma^2e+2\gamma x+Bx,\qquad
   w_h(cAc)=\gamma^3\lambda_h+3\gamma^2\lambda_{h+1}
                                +2\gamma M_2+\gamma L+dL.
\]
The right side of the mixed equality in (4) is
\(3(\gamma^3\lambda_h+3\gamma^2\lambda_{h+1}+3\gamma L+\lambda_s)\).
Consequently, using (5) and (2),
\[
                          dL=2\gamma^2\lambda_{s-2}+4\gamma L,
                    \qquad d=2a .
 \tag{7}
\]
This is a genuine branching payment: a single mixed rooted fork
determines the third clock by using the one-dimensional contributing
part of \(Bx\). It is not a scalar test. The clocks \(x\) on contributing
rows are now \(0,a,2a\), so the paid moments at \(h=s-3\) satisfy
\(M_3-3aM_2+2a^2M_1=0\).

Put \(r=s-1,\ t=a/\gamma,\ v=t-2,\ Q=\gamma^2\lambda_{s-3}/L\).
By (6) and (1) one has
\(v=\gamma\lambda_{s-2}/L\) and
\[
             (r-1)Q=r v^2+2v-r-1.
\]
Dividing the three-point moment identity by \(\gamma L\) gives
\((2-3t)Q+(9-6t+2t^2)v+12-6t=0\). Substitute \(v=t-2\) and multiply
by \(-(r-1)\) to obtain the cubic
\[
          C_s(t)=(s+1)t^3-4s t^2+2(s-3)t+4=0,\qquad
          t=\frac{1/\gamma-2}{s-1}.
 \tag{8}
\]
All algebra to this point needs only the relevant scalar units and
payment through order \(s+1\); the following exclusion is char-zero.

## 3. No scalar/branching compatibility in characteristic zero

The monic integer polynomial
\[
 F_s(X)=\sum_{j=0}^s(-1)^{s-j}
             \binom{s}{j}\frac{(s+1)!}{(j+1)!}X^j
       =(-1)^s s!L_s^{(1)}(X)
\]
vanishes at \(X=1/\gamma\) by (2) and the explicit \(\lambda_s\).
Indeed \(F_s(1/\gamma)=(s+1)!\gamma^{-s}\lambda_s\).
By the classical Schur irreducibility of literal \(L_s^{(1)}\) over
\(\mathbb Q\), an element satisfying \(F_s(X)=0\) has degree \(s\)
over the prime subfield. The nonzero cubic (8) in
\(t=(X-2)/(s-1)\) is impossible when \(s\ge4\).
For confirmation of precisely the associated alpha-one assertion see
Farshid Hajir, "Algebraic properties of a family of generalized Laguerre
polynomials," p. 584:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/0E2DDA7A33FA3B483679E4693D093D36/S0008414X00000882a.pdf/algebraic-properties-of-a-family-of-generalized-laguerre-polynomials.pdf

Here a completely standalone arithmetic argument also suffices; it
excludes just the common factors of degree at most three needed by (8).
It appears in the appendix. The result is independent of how a
characteristic-zero field embeds any of the roots; the rational
polynomials have no common root in an algebraic closure. This finishes
the theorem.

The gained stage is genuinely absent from the scalar cap. Over an
algebraic closure, choose a nonzero root \(X\) of \(F_s\) and set
\(\gamma=1/X\). For \(B\) with unit subdiagonal and all other entries
zero, the columns \(e,Be,\ldots,B^{s-1}e\) are independent by their
first nonzero coordinates. Choose \(b\) so its evaluations on these
columns are \(\lambda_0,\ldots,\lambda_{s-1}\). The paid value
\(\lambda_s=0=b^TB^se\) is automatic. Expanding \(A=\gamma I+B\)
then gives all tall conditions through \(s+1\); the nonlinear
contradiction is additional. This example asserts no stability
condition and no nonlinear attainment.

## Appendix. Elementary exclusion without full irreducibility

Suppose \(F_s(X)\) and
\[
       N_s(X)=(s-1)^3 C_s((X-2)/(s-1))
\]
shared an irreducible rational factor \(G\) of degree \(k\le3\).
As \(F_s\) is monic integral, \(G\) can be taken monic integral.
Let \(\ell\) be a rational prime and normalize an extended \(\ell\)-adic
valuation by \(v_\ell(\ell)=1\). All roots of \(F_s\) have valuation
between 0 and \(1/(\ell-1)\). Nonnegativity follows from monicity,
since otherwise the leading term is the unique least-valuation
term. For the upper bound, the coefficient \(a_j\) at \(X^j\)
satisfies
\[
   v_\ell(a_j)\ge v_\ell((s+1)!)-v_\ell((j+1)!),\qquad
   v_\ell((j+1)!)\le j/(\ell-1).
\]
For the last inequality use Legendre's formula with digit sum at least
one. If a root had larger valuation, the constant term would be the
unique least-valuation term. Both conclusions follow.

Whenever \(\ell\) divides one of \(s-k+2,\ldots,s+1\), the
coefficients through \(j=s-k\) vanish modulo \(\ell\), so
\(X^{s-k+1}\mid F_s\bmod\ell\).
Then \(\ell\) divides \(G(0)\): otherwise the monic cofactor of
degree \(s-k\) would have all that \(X\)-multiplicity. Together
with the bound on all \(k\) root valuations this is impossible if
\(\ell\ge k+2\), since
\(1\le v_\ell(G(0))\le k/(\ell-1)<1\).

* For \(k=3\), among \(s-1,s,s+1\) there is a prime divisor at least
  five. If \(s\) is even, one of its odd neighbors is not divisible by
  three. If \(s\) is odd and not divisible by three, use \(s\).
  Otherwise its two even neighbors are both prime to three; they
  cannot both be powers of two differing by two, since the only such
  positive powers are 2 and 4 and \(s\ge4\).
* For \(k=1\), an odd prime divisor of \(s+1\) suffices. If
  \(s+1=2^a\) with \(a\ge3\), a rational root \(X\) of \(G\) must
  have \(v_2(X)=1\), by the same two bounds at \(\ell=2\).
  Thus \(X\equiv2\pmod4\) and \(v_2(t)\ge1\) for
  \(t=(X-2)/(s-1)\), since \(v_2(s-1)=1\). In \(C_s(t)\), the
  constant four has valuation two, and every other term has
  valuation at least four (also \(4\mid s-3\)). This precludes zero.
* For \(k=2\), a prime at least five dividing \(s\) or \(s+1\)
  suffices. Otherwise these two coprime integers must be an
  adjacent power of two and power of three. The only such ordered
  pairs, above \(s\ge4\), are \((8,9)\): if \(3^b+1=2^a\),
  reduction modulo eight excludes \(a\ge3\); if \(2^a+1=3^b\)
  and \(a\ge3\), that reduction forces \(b\) even and
  \(3^{b/2}-1,3^{b/2}+1\) are powers of two differing by two, giving
  \(b=2,a=3\). The cases \(a\le2\) do not reach \(s\ge4\).
  For \(s=8\), use \(\ell=3\) to get \(v_3(G(0))\ge1\) and both
  root valuations at most \(1/2\), so each is exactly \(1/2\).
  But
  \[
                   N_8(X)=9X^3-278X^2+1494X-576.
  \]
  At a root of valuation \(1/2\), the \(X^2\) term has valuation
  one and is uniquely of least valuation, again impossible.

These exhaust the degrees and establish the required coprimality.
