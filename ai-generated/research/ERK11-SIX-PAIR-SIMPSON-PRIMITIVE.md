# Exact projected primitives on the six-pair scalar slots

Continue [the six-pair site decomposition](ERK11-SIX-PAIR-SITE-MASK.md), including exactly twelve active physical rows and six noncarrier pairs. The field has characteristic zero. This refines the literal primitive projection; it is not a stage deletion or an exclusion of the six-pair case.

Let \(\pi_{\mathcal Q}\) project onto the nine scalar slots, zeroing response and carrier components, and let \(\iota_{\mathcal Q}\) embed them as pair-constant and dormant numerical slots with zero carrier values. The reduced matrices \(\widehat A=\pi_{\mathcal Q}A\iota_{\mathcal Q}\) and \(\widehat A^\star=\pi_{\mathcal Q}A^\star\iota_{\mathcal Q}\) are adjoint for the actual scalar-slot diagonal form (pair masses and dormant physical weights). Neither reduced matrix is asserted explicit: a pair mean may read a scalar slot whose other member is later in physical order.

For every scalar clock polynomial of degree at most three these two reduced matrices apply the exact left and right primitives stagewise. The scalar numerical representative is \(P(\mathbf c)-P(\theta)\boldsymbol s\), with carrier values zero. Its unary primitive is actual, and the difference from the degree-at-most-four clock model is in \(F_4\) or its reflected counterpart \(\bar F_4\). The entire pure space disappears on scalar projection. Thus this is a statement about the actual projected operators, not fitted reduced arrays.

## A live left plateau pair

Assume physical rows 4 and 5 are both response-active at the physical left plateau clock \(a=2c_3\ne0\). They are then precisely the two members of that active pair. In the reduced left row at \(a\), strictness confines its scalar donors to the physical origin, the scalar slot of physical row 3 at \(a/2\), and its own scalar slot at \(a\), with distinct clocks. The carrier datum is zero under \(\iota_{\mathcal Q}\). The three local scalar weights are exactly \((a/6,2a/3,a/6)\), by applying primitive exactness to \(1,X,X^2\) and using three-node Vandermonde uniqueness. This is a literal Simpson row, regardless of the weight signs or the position of row 3's partner.

For a quartic polynomial, the left scalar primitive deficit is a multiple of the extra scalar pure direction \(\boldsymbol h^0\); it vanishes for lower-degree inputs. With the two-front normalization \(h^0(a)=-1\), the exact projected law is
\[
   \widehat A P(\mathbf c)=(JP)(\mathbf c)
         -\frac{a^5}{120}[X^4]P\,\boldsymbol h^0
         \qquad(\deg P\le4).
\]
The coefficient is measured at the actual scalar plateau: the Simpson value on \(X^4\) is \(5a^5/24\), while the model is \(a^5/5\). No degree-six model is used.

The response primitive also has an exact normalization. For \(\boldsymbol F=\theta\boldsymbol r\) as in the six-pair note, use the actual left first-five coefficients
\[
       F_4=-a^2/2,\qquad A_{54}=(F_5-F_4)/(3a).
\]
At row 5, the vector \(A(C-aI/2)\boldsymbol F\) has only the row-4 donor contribution, equal to \((a/2)F_4 A_{54}\). At row 4 it is zero by strictness. The weight of row 5 in its pair average is \(-F_4/(F_5-F_4)\), because the first pooled response is zero. The actual scalar projection is therefore \(-a^4/24\) at the plateau. The remaining projected values are fixed by the same multiple of \(\boldsymbol h^0\), because \(A(C-aI/2)\boldsymbol F\) is pure of grade five and \(\pi_{\mathcal Q}A\boldsymbol F=0\). Hence
\[
       \pi_{\mathcal Q}AC\boldsymbol F=\frac{a^4}{24}\boldsymbol h^0 .
\]
In particular the projected scalar deficit through quartic degree is removed by adding \((a/5)[X^4]P\, C\boldsymbol F\) to the actual input before applying \(A\) and projecting. This does not erase the response component.

## Reflected primitive

If both reverse clean plateau rows (physical 14 and 13) are active, write \(b=1-c_{14}\) for the nonzero reflected plateau clock and \(\boldsymbol G=(1-\theta)A^\star\boldsymbol s=\kappa\boldsymbol F\) for its physical response scale. In the reflected clock \(Y=1-X\), the projected right row has the same scalar weights \((b/6,2b/3,b/6)\) on its origin, half-plateau, and plateau slots. For a model polynomial in \(Y\), its exact quartic scalar deficit is \(-b^5\bar{\boldsymbol h}^0/120\) times its quartic coefficient. The response coupling \(\pi_{\mathcal Q}A^\star(I-C)\boldsymbol G\) is \(b^4\bar{\boldsymbol h}^0/24\), so in physical left variables
\[
        \pi_{\mathcal Q}A^\star C\boldsymbol F
                    =-\frac{b^4}{24\kappa}\bar{\boldsymbol h}^0 .
\]
The reverse deductions use grades at most five; no reverse grade-ten pure square is used.

[The Lean scalar gate](../lean/RKCert/Research/ERK11SixPairPrimitiveGate.lean) checks the exact Simpson moments and two-stage weighted response identities on Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1. The projected and physical support arguments above are mathematical.
