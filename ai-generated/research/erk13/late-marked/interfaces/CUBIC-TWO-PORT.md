# The native cubic two-port scalar obstruction

Let P∈K[X] be nonzero, deg P≤3, over a characteristic-zero field. Suppose s,t∈K are nonzero and distinct, that the three primitives primitive(X^(k+1)P)(s)=0 for k=0,1,2, and that two more primitives primitive(X^k X(X−s)P)(t)=0 for k=0,1. These hypotheses are inconsistent.

Divide by the nonzero powers of a₀ and scale the independent variable, writing t=a₁/a₀ and P̃(T)=P(a₀ T). The first three weight-X moments of P̃ are zero at 1. If deg P≤2 they force P̃=0 by the checked weight-X Cauchy detector. If deg P=3, comparing its leading coefficient with the monic polynomial

    H₃(T)=T³−(12/7)T²+(6/7)T−4/35

gives P̃ proportional to H₃: three literal integrations show the same moments for H₃, and the difference has degree≤2. The two second primitives (after nonzero scaling) are

    t²(t−1)²(5t−2)(7t−6)/210,
    t³(t−1)²(30t²−35t+8)/210.

Since t≠0,1, the first gives t=2/5 or t=6/7; in the second the last quadratic evaluates to −6/5 or 2/49, both nonzero. This is native scalar algebra for this order-13 port, not any external low-order method classification or fixed tableau.

See the checked [NativeCubicTwoPort source](../../../../lean/RKCert/ReviewedNative/NativeCubicTwoPort.lean). This is the scalar leaf only. Both its late physical uses are proved in [paid staircase](../PAID-STAIRCASE.md) and [late square](../LATE-SQUARE.md); no ordinary zero/nonzero seed hypothesis is taken from the scalar leaf.
