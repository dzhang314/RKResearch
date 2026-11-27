# The unbalanced all-live independent ERK10 branch is impossible

Work over an arbitrary characteristic-zero field. In the
[fourteen-stage equality analysis](ERK10-FOURTEEN-STAGE-EQUALITY.md)
assume every output weight is nonzero and \(d,Cd\) are independent.
That analysis showed there is a genuine quadratic shape \(G_{\rm raw}\)
with \(d_i=G_{\rm raw}(c_i)\) at dirty rows. The **unbalanced** case
has exactly nine distinct active dirty rows and five distinct clean
rows, with clean clocks \(0,u,w,v,1\) in their literal chronology.
Its two clean-boundary primitive identities are exact. This note
excludes the whole unbalanced case in characteristic zero.

Together with the
[balanced nonexistence theorem](ERK10-BALANCED-SEAM-EXCLUSION.md),
there cannot be an all-live fourteen-stage order-ten tableau with
\(d,Cd\) independent. This does **not** exclude the \(d,Cd\)-dependent
case or any zero-output-weight case, and does not change the 14–15
unrestricted interval.

## Exact clean moments and one more paid primitive

The eight paid tests \(bC^k d=0\) for \(0\le k\le7\)
give genuine G-weighted quadrature on the five clean rows.
The nine dirty weights obey the single barycentric relation
\(b_iG_{\rm raw}(c_i)=\kappa/D'(c_i)\) for their monic hull \(D\),
but their values need not be reconstructed here. In particular write
\(G\) for the monic normalization of \(G_{\rm raw}\); the following
three identities hold from the G-weighted tests:
\[
  \int_0^1 X(1-X)G(X)(X-u)(X-w)(X-v)X^j\,dX=0,
                                             \quad j=0,1,2 .    \tag{1}
\]
The tested polynomial before multiplying by \(G\) has degree at
most seven, so the use of \(d\) costs at most nine.

For a new mixed primitive condition take the actual clean-only
grade-two vector \(T=G_{\rm raw}(c)-d\). Then
\(V_L=C(C-u)T\) can be nonzero only at the three clean rows
with clocks \(w,v,1\), and \(V_R=(C-v)(C-1)T\) only at
the clean rows with clocks \(0,u,w\). By strictness \(A V_L\)
is zero through the literal clean row at \(w\). Thus the actual
product of \(A V_L\) and \(V_R\) is zero. Its total grade is
\(4+1+4=9\). Cancelling the common leading scale proves
\[
  \int_0^1 J[G(X)X(X-u)]\ G(X)(X-v)(X-1)\,dX=0 .               \tag{2}
\]
No first-half/last-half numerical support assumption, or equality
of the two grade-five pure maps, enters this test. The reversal is
used only through the genuinely paid reverse low-grade primitive
in the earlier ledger.

## Centering and all special cases

Put \(Z=2X-1\), \(U=2u-1,V=2v-1,W=2w-1\).
Write the centered monic quadratic as \(Z^2-SZ+P\). Let
\(m=(U+V)/2\), \(h=(U-V)/2\), \(\delta=1-2h\),
\(\alpha=1-3h\). The first and reflected last clean primitive
tests become
\[
 m(3h-1)+\delta S=0,\qquad
 6P=4Sm-3(m^2+h^2)+2h-1 .                               \tag{3}
\]
For example before sum and difference their centered equations
are \(3U^2-(2+4S)U+1+2S+6P=0\) and
\(3V^2+(2-4S)V+1-2S+6P=0\).

Write
\[
 (Z^2-SZ+P)(Z-U)(Z-V)=Z^4+b_3Z^3+b_2Z^2+b_1Z+b_0 .
\]
Equation (1) says that multiplying this quartic by \(Z-W\)
is orthogonal to \(1,Z,Z^2\) under \(1-Z^2\) on \([-1,1]\).
Using the moments \(4/[(2j+1)(2j+3)]\) of \(Z^{2j}\),
the equivalent three equations are
\[
 \begin{split}
 3b_1+2b_3&=W(3b_2+2),\\
 b_3&=W(1-21b_0),\\
 5+9b_2+21b_0&=W(9b_3+21b_1).
 \end{split}                                                   \tag{4}
\]
Here the two cleared even moment equations on quintic
coefficients \(A_4,A_2,A_0\) are
\(3A_4+7A_2+35A_0=5A_4+9A_2+21A_0=0\);
they give \(3A_2=-2A_4,\ 21A_0=A_4\).
The odd moment gives \(5+9A_3+21A_1=0\).

* If \(\delta=0\), equation (3) forces \(m=0\) and
  \(P=-1/8\). Thus \(U,V=1/2,-1/2\).
  The same three moments of
  \((Z^2-SZ-1/8)(Z^2-1/4)(Z-W)\) give
  \(40S+47W=88S+73W=120SW+73=0\).
  The first two force \(S=W=0\) (determinant \(-1216\)),
  contradicting the third.
* If \(\delta\ne0,m=0\), then \(S=0\),
  \(P=(-3h^2+2h-1)/6\), \(b_3=b_1=0\),
  \(b_2=P-h^2,\ b_0=-P h^2\).
  In case \(W\ne0\), equations (4) give \(b_2=-2/3\)
  and \(b_0=1/21\). Thus \(h\) satisfies both
  \(21h^4-14h^2+1=0\) and \(9h^2-2h-3=0\),
  contradicted by the earlier exact opposite-Lobatto Bézout
  constant 248.
* In the remaining symmetric case \(m=W=0,\delta\ne0\),
  the third equation of (4), multiplied by 2, factors as
  \((h-1)(21h^3+7h^2-13h-7)=0\). The first factor is
  nonzero because \(h=1\) would give \(u=1\).
  Clearing the centered mixed primitive (2) gives
  \(4725h^6-4410h^5-1365h^4+1140h^3+715h^2-250h-107=0\).
  Those two polynomial equations have an explicit Bézout
  constant 1664512, checked by the companion.

## The generic eliminant and portable integer proof

Assume \(\delta m\ne0\) and put \(t=m^2,\ k=W/m\).
Define
\[
 \begin{split}
 s&=6\delta,\qquad
 N=4\alpha t-3\delta(t+h^2)+2\delta h-\delta ,\\
 K_3&=-12\delta-6\alpha,\qquad
 K_2=6\delta(t-h^2)+12\alpha t+N,\\
 K_1&=-6\alpha(t-h^2)-2N,\qquad
 K_0=N(t-h^2).
 \end{split}
\]
Equations (3) show that \(S=\alpha m/\delta,\ P=N/s\).
Thus \(K_3,K_1\) are \(s/m\) times \(b_3,b_1\);
\(K_2,K_0\) are \(s\) times \(b_2,b_0\).
Eliminating \(k\) between first–second and first–third equations
of (4), without cancelling an equation coefficient, gives the
two cubics in \(t\)
\[
 \begin{split}
 18F_0&=(3K_1+2K_3)(s-21K_0)-K_3(3K_2+2s),\\
 9F_1&=(3K_1+2K_3)t(9K_3+21K_1)
                  -(5s+9K_2+21K_0)(3K_2+2s).
 \end{split}
\]
Both vanish.

For the third cubic \(B(h,t)\), use the centered scaled
quadratic \(\widetilde G=sZ^2-6\alpha m Z+N\).
Let \(l,r\) be the coefficient vectors of
\(\widetilde G(Z+1)(Z-m-h)\) and
\(\widetilde G(Z-1)(Z-m+h)\), respectively.
The matrix \(M\) with entry
\(1575\int_{-1}^1(\int_{-1}^Z T^i dT)Z^j dZ\) is integer,
and explicitly printed in the companion. Then
\(2B(h,m^2)=l^\mathsf T M r\), so (2) gives \(B(h,t)=0\).
All centering and scaling factors are nonzero on this branch.
The polynomial \(B\) has integer coefficients, \(t\)-degree at
most three and \(h\)-degree at most eight.

The two exact cubic-in-\(t\) resultants factor as
\[
 \begin{split}
 {\rm Res}_t(F_0,B)&=112896(2h-1)(6h-1)P_{19}(h),\\
 {\rm Res}_t(F_1,B)&=-43008(2h-1)^2 Q_{22}(h).
 \end{split}
\]
The integer polynomials \(P_{19}\) and \(Q_{22}\) are listed by
Horner coefficients in [ERK10UnbalancedGate.lean](../lean/RKCert/Research/ERK10UnbalancedGate.lean).
The coefficient computations are exact without a symbolic
algebra dependency in Lean:
1. The \(F_0,F_1\) formulas are checked on nine by four integer
   points; their degrees are at most \(8,3\), so interpolation
   proves the polynomial identities. For \(2B(h,m^2)=l^\mathsf
   TMr\), nine by seven points similarly cover degrees \(8,6\).
2. The displayed resultant factorizations are checked on
   49 integer points. This suffices for the exact identities
   by the Sylvester determinant bound \(3\cdot8+3\cdot8=48\).
   The companion uses the ordinary expanded cubic resultant
   polynomial (the 6-by-6 Sylvester determinant).
3. In \(\mathbb F_{47}[h]\), the polynomials
   \((6h-1)P_{19}\) and \(Q_{22}\) have their full respective
   degrees 20 and 22, and satisfy a Bézout identity with
   explicitly listed degrees 21 and 19 for the two multipliers.
   Forty-two distinct residues check that identity, whose
   total degree is at most 41. This proves the original
   two integer polynomials coprime over \(\mathbb Q\):
   a nonconstant primitive common factor would still have
   nonzero leading coefficient modulo 47, because both
   product leading coefficients are nonzero there.

A shared finite root \(t\) makes both Sylvester determinants
zero even if a specialized leading \(t\)-coefficient vanishes.
Since \(2h-1\ne0\), the two now force \(h\) to be a common
root of coprime polynomials over \(\mathbb Q\), impossible
over any characteristic-zero field. This exhausts the generic
case and completes the unbalanced exclusion.

The Lean companion checks the integer-grid identities, the
modular Bézout and leading guards, and the exceptional scalar
cases. The interpolation, resultant interpretation and actual
stage-profile bridges are given mathematically above. No
full native 14-stage lower theorem is claimed.
