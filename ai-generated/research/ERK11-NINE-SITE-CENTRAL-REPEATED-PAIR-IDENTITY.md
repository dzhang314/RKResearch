# A paid central repeated-pair clock identity in ERK11

**Scope.** In the all-live both-new two-front chart, let the actual
inner rows 8 and 10 be the same active pair clock \(u\), and let
physical 9 be the internal response-zero noncarrier at clock
\(\zeta\). The characteristic-zero identity below uses no shifted
Hankel solve and no division by \(\zeta-u\). The sign corollaries
are ordered-field statements. It applies to both repeated-inner
pair geometries of the [nine-site remainder](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).

## Actual supports and grade ledger

The forward grade-four square-clock vector \(V_L\) has model
\(V_a=X^2(X-a)^2\) and vanishes at physical 1–7. The reflected
grade-four vector \(V_R\) has model
\(V_b=(1-X)^2(X-d)^2\) and vanishes at physical 11–17.
These are the two actual both-new boundary vanishing statements,
not arbitrary fitted polynomials. At the dormant row their
numerical values are \(V_a(\zeta),V_b(\zeta)\), because the
response and carrier reads there are both zero.

Strict lower \(A\) makes \(AV_L\) vanish at physical 1–8.
Strict upper \(A^\star=B^{-1}A^{\mathsf T}B\) makes
\(A^\star V_R\) vanish at physical 10–17. Their models are
respectively \(P=JV_a\) and \(Q=\bar J V_b\), with \(J\)
the primitive anchored at 0 and \(\bar J\) at 1. The four
actual componentwise products therefore have supports contained in
\[
\begin{array}{c|c|c}
 \text{product}&\text{possible physical support}&
   \text{grade and extra clock allowance used}\\ \hline
 V_LV_R&8,9,10&4+4+2=10\\
 (AV_L)V_R&9,10&5+4+1=10\\
 V_L(A^\star V_R)&8,9&4+5+1=10\\
 (AV_L)(A^\star V_R)&9&5+5=10 .
\end{array}
\]
All pairings are the paid forward/reverse mixed pairings:
these vectors already vanish through the corresponding
six-row anchor. Inserting \(C\) in a grade-four factor
gives an actual grade-five anchored vector with model
multiplied by \(X\). Thus the same mixed grade-five Gram
pays the middle two lines, even with one clock.
The last line pairs two literal anchored fifth-grade
primitives. It is **not** the square of a reverse
fifth-grade pure vector. No ordinary reverse order eleven
is used.

## Clock identity, including a possible alias

Define the rational polynomial integrals
\[
 \begin{aligned}
 H&=\int_0^1 PV_b=\int_0^1 V_aQ,&
 C_1&=\int_0^1 XPV_b,& C_2&=\int_0^1 XV_aQ,\\
 J_0&=\int_0^1 PQ,&
 W&=V_aV_b,& I_{uu}&=\int_0^1 W(X)(X-u)^2.
 \end{aligned}
\]
The equality for \(H\) is primitive adjointness, or integration
by parts with \(P(0)=Q(1)=0\). The exact supports above give
\[
 \begin{split}
 C_1-uH&=b_9(\zeta-u)(AV_L)_9\,V_b(\zeta),\\
 C_2-uH&=b_9(\zeta-u)V_a(\zeta)\,(A^\star V_R)_9,\\
 J_0&=b_9(AV_L)_9(A^\star V_R)_9,\\
 I_{uu}&=b_9(\zeta-u)^2 W(\zeta).
 \end{split}
\]
In the first two equations the active \(u\) slot is killed
by one clock difference. In the last equation both occurrences
of \(u\) are killed by the clock square. Multiplying the
first two equations and substituting the last two gives
\[
 \boxed{(C_1-uH)(C_2-uH)=J_0 I_{uu}.}
\]
This is a quadratic in \(u\) with coefficients depending
only on the two widths; \(\zeta\), \(b_9\), the primitive
tap amplitudes, and any shifted-pivot choices have disappeared.

No step divides by the clock difference. Thus if \(\zeta=u\)
the same literal proof gives \(I_{uu}=0\) (and \(C_i=uH\)).
Over an ordered field \(W(X)(X-u)^2\) is a nonzero polynomial
square, so its strictly positive rational Gram makes this
impossible. Over an unordered characteristic-zero field it
is an exact algebraic constraint, not a positivity inference.
For a genuine \(\zeta\ne u\) the univariate identity is
available without any endpoint or polynomial factor
cancellation.

Over an ordered field \(H>0\) and \(J_0>0\) by the nonzero
square simplex integrals for the two primitives, and
\(I_{uu}>0\) by the weighted square. Hence the actual
\(u\) is strictly outside the closed interval with endpoints
\(C_1/H,C_2/H\). The last displayed weight identity also
forces \(b_9>0\) when \(\zeta\) is genuine and nonendpoint.
These are separate necessary signs, not a claim that the
quadratic by itself lacks real roots.

The [native scalar product and alias identities](../lean/RKCert/ReviewedNative/ERK11CentralRepeatedPairProductGate.lean)
hold over any commutative ring and pass all four
[Lean checks](erk11-central-repeated-pair/lean-replay.txt).
The support and paid grade ledger above is the mathematical ingress
from an actual tableau.
