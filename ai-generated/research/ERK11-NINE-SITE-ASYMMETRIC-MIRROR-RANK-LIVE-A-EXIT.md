# Mirrored variable edge: exclude singular mixed determinant with A0 live

**Scope.** Continue the [mirrored finite atlas](ERK11-NINE-SITE-ASYMMETRIC-MIRRORED-FINITE.md):
right extras \(\{h,t\}\), left extras \(\{t,s\}\), genuine
dormant physical 8 followed by \(e,s\). The actual affine
slope is known live. This excludes the entire
\(A_0D_0-B_0C_0=0,\ A_0\ne0\) branch over characteristic
zero. Together with the [A0=0 exclusion](ERK11-NINE-SITE-ASYMMETRIC-MIRROR-RANK-A0-EXIT.md),
only the nondegenerate mixed-determinant part of this
mirrored variable edge remains. None of this excludes
other asymmetric edge orders.

## The four width norms in the actual two-node measure

The rank-one middle equation and live \(A_0\) fix
\(s=-B_0/A_0\). Write \(E_s=A_0,N_s=-B_0\). Define
the actual width-moment hull
\[
 P_5(X)=P_4(X)(E_s X-N_s),\qquad
 m_j=\int X(1-X)P_5(X)X^j,\quad 0\le j\le3.
\]
The two remaining modified scalar sites are the true
\(t,z\), distinct and with live signed weights; the
common factor \(E_s\) is live. Its paid two-site
pivot \(\delta=m_0m_2-m_1^2\ne0\) and Cramer data
\(\sigma=m_0m_3-m_1m_2,\ \pi=m_1m_3-m_2^2\)
give \(Y=\delta t,\ Z=\delta z=\sigma-Y\) and the true
\(Y^2-\sigma Y+\delta\pi=0\).

Let
\[
 L_0=(aE_s-N_s)(a\delta-Y),\quad L_1=-N_sY,\quad
 R_0=(h-d)(Y-d\delta),\quad R_1=-(1-h)(\delta-Y).
\]
These are the same actual derivative rows up to the
live scales, with the left extras \(t,s\) and right
extras \(h,t\). The following four polynomial contacts
are genuine at the actual root:
* \(F_{\rm raw}\): the standard first derivative Gram
  with precisely these scaled row coefficients.
* \(G_{\rm raw}\): the physical-8 dormant-left port with
  \(R_0K_0(Z/\delta)+R_1K_1(Z/\delta)\), cleared by
  \(\delta^3\). The forward primitive is literally zero there.
* \(M_{\rm raw}\): the same true [physical-9 weighted right
  repeat](ERK11-NINE-SITE-ASYMMETRIC-MIRRORED-FINITE.md),
  evaluated at the fixed \(s\) and the scaled left row.
  This is not the physical-10 direct half mark.
* \(S_{\rm raw}\): the true dormant support
  \(I(e,s)(z-h)(z-t)=q_0 z(1-z)(z-a)(z-d)\).
  With the width-scaled moments above,
  \(q_0=(m_1-t m_0)/E_s\) exactly, so the receipt clears
  the live \(E_s,\delta\). No individual primitive is
  divided out in this or the preceding mark.

Reduce each polynomial in \(Y\) modulo the actual monic
quadratic. If its remainder is \(uY+v\), its norm
\(v^2+\sigma uv+\delta\pi u^2\) vanishes. Thus these four
contacts give necessary **width** polynomials \(F,G,M,S\).
Only factors of known live widths, the shifted pivot,
the discriminant and actual clock differences are removed.

## Exact exceptional coefficients, not just a projection

The vanishing mixed determinant forces \(J_0=0\) or
\(R_{33}=0\). On \(J_0=0\), the exact \(b\)-resultants
of that width polynomial against \(F,G,S\) have
\(a\)-degrees \(152,228,200\). Their monic common gcd
is \(F_8^6\) with \(F_8\) irreducible of degree eight.
The weighted mark can vanish on \(J_0=0\) and is not needed
in this projection.

On \(R_{33}=0\), use \(F,G,M,S\). The corresponding exact
degrees are \(234,342,228,300\), and the common gcd is
\(F_{12}^6\) with \(F_{12}\) irreducible of degree twelve.
The resultants remain necessary at degree-drop widths.

Now compute the exact common polynomials in \(b\) over
\(\mathbf Q[a]/F_8\) and \(\mathbf Q[a]/F_{12}\) respectively,
using each width locus and its full list of necessary norms.
Both exact gcds are monic linear, and each divides \(A_0\)
in its coefficient field. The receipt checks those zero
remainders directly. Hence any actual finite \(b\) would
have \(A_0=0\), contradicting the present live guard.
This handles every embedding, without assuming that an
\(a\)-projection factor has only its expected \(b\) fiber.

The standalone proof is entirely exact rational arithmetic.
The norm and affine scalar identities have earlier Lean
counterparts, but the combined field gcds are not claimed
as kernel computations.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-mirror-rank-live-a-exit/) are included.
