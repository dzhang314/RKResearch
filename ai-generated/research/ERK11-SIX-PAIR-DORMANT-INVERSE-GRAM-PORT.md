# Pivot-free inverse-Gram equations for the genuine dormant site

**Scope.** Continue the [nine-live-site remainder](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
of the exactly two-carrier, six-active-pair, both-new ERK11 chart.
The unique internal response-zero noncarrier is at physical \(i=8,9,10\)
and its clock \(\zeta\) is new and nonendpoint. The equations below
are necessary over a characteristic-zero field given those premises.
They are not an exclusion of the nine-site chart.

Let \(\langle\ ,\ \rangle\) denote the **full** inverse anchored Gram
pairing, including the normalization factor 210 in the monomial
bases. On the left anchored model space write
\(\ell_y:P\mapsto P(y)\); on the reflected model space write
\(r_y:Q\mapsto Q(y)\) in the physical clock coordinate.
Let \(\Phi_L,\Phi_R\) be the derivative row functionals of the
earlier clock atlas, up to their proven-live actual row-7 and
row-11 prefactors. The inverse Gram pairs physical rows 7–11
to the diagonal reciprocal weights. In particular
\[
 \langle L_j,R_k\rangle=0\quad(j\ne k),\qquad
 \langle L_j,R_j\rangle=1/b_j .
\]

On the dormant row the response and carrier coordinates vanish.
Hence the actual anchored rows always have the form
\[
 L_i=\ell_\zeta+h_L\ell_a,\qquad
 R_i=r_\zeta+h_Rr_d
\]
for some scalar reads \(h_L,h_R\). This is the known grade-five
lift formula; the subtraction of a quadratic times the response
does not affect the dormant read. Set
\[
 \begin{array}{ll}
 A_L=\langle\ell_a,\Phi_R\rangle, &
 B_L=\langle\ell_\zeta,\Phi_R\rangle,\\
 A_R=\langle\Phi_L,r_d\rangle, &
 B_R=\langle\Phi_L,r_\zeta\rangle,
 \end{array}
 \qquad
 \widehat L=A_L\ell_\zeta-B_L\ell_a,\quad
 \widehat R=A_R r_\zeta-B_R r_d .
\]
Because \(i\ne7,11\), the two off-diagonals give
\(B_L+h_L A_L=B_R+h_R A_R=0\). Hence
\(\widehat L=A_LL_i,\ \widehat R=A_RR_i\),
even on a zero pivot. In particular \(A_L=0\) forces
\(B_L=0\), and \(A_R=0\) forces \(B_R=0\); we do not
divide by either.

Write \(P_a=J[X^2(X-a)^2]\) and its reflected counterpart
\(P_b\) in \(Y=1-X\). Define
\[
 D_\zeta(P)=a^5P(\zeta)-30P(a)P_a(\zeta),
 \qquad
 D^{R}_{1-\zeta}(Q)=b^5Q(\zeta)-30 Q(d)P_b(1-\zeta).
\]
The first square-clock vector vanishes through its seventh
row, so its literal primitive vanishes through its eighth;
use the reflected statement separately on the right.
At dormant physical 8 this says
\(L_8=D_\zeta/a^5\). At dormant physical 10 it says
\(R_{10}=D^R_{1-\zeta}/b^5\). Neither such automatic
primitive zero is used at physical 9.

We obtain the following necessary identities:
\[
\begin{array}{c|l|l}
i & \text{extra off-diagonal} & \text{diagonal after clearing}\\ \hline
8&\langle D_\zeta,\Phi_R\rangle=0&
 b_i\langle D_\zeta,\widehat R\rangle=a^5 A_R\\
9&\text{the two }B+hA\text{ relations above}&
 b_i\langle\widehat L,\widehat R\rangle=A_L A_R\\
10&\langle\Phi_L,D^R_{1-\zeta}\rangle=0&
 b_i\langle\widehat L,D^R_{1-\zeta}\rangle=b^5 A_L .
\end{array}
\]
Each follows from the displayed actual row expressions and
the same reciprocal-weight diagonal. The prefactor choices
for \(\Phi\) do not matter: both sides scale identically.

Finally all nine scalar sites are distinct and live. If
\(H_6\) is the monic active hull, the degree-eight scalar
Lagrange weight at the dormant equals its individual
physical weight, hence
\[
 b_i=\frac{\displaystyle\int_0^1 X(X-1)H_6(X)\,dX}
              {\zeta(\zeta-1)H_6(\zeta)} .
\]
The denominator is live by the separation theorem, and the
numerator is live as well because \(b_i\ne0\). Substitute
this formula and clear the actual denominator to make
each diagonal an equation solely in the clock variables.
No hypothetical stage matrix, generic pivot, or reverse
order eleven is used. The needed pairings are exactly the
known mixed grade-five Gram and ordinary paid degree-eight
scalar quadrature.

The [Lean algebra companion](../lean/RKCert/ReviewedNative/ERK11DormantInverseGramPort.lean)
checks the two pivot-free pairing expansions and denominator
clearing over a commutative ring. The actual rooted-space and
quadrature hypotheses above are mathematical.
