# Native characteristic exclusions for the four-zero Gaussian rear charts

This is a Lean verification of the **complete scalar characteristic projection** in the [Gaussian rear census](../sdirk-eight-four-zero-gaussian-rear/README.md). It is independent of Python resultants. The paper still supplies the rooted flag and literal chronology reductions, and the finite fibers at the exceptional primes; this supplement does not claim a native end-to-end `HasOrder` theorem.

Let $L(X)=70X^4-140X^3+90X^2-20X+1$ and use its first two polynomial divided differences (computed integrally, not by evaluating divisions). The native file checks five denominator-free integer Bézout identities. In each case the left side is a linear combination of the three necessary polynomial equations, so any solution forces the displayed integer to vanish in its coefficient domain:

| Scalar chart | Forced zero integer |
| --- | ---: |
| No active off-zero clock, third reverse stage silent | $27019898606=2\cdot397\cdot487\cdot69877$ |
| No active off-zero clock, live arithmetic third | $30=2\cdot3\cdot5$ |
| No active off-zero clock, live star third | $7544374=2\cdot37\cdot269\cdot379$ |
| One canceled active off-zero clock, live arithmetic third | $13645543=17\cdot103\cdot7793$ |
| One canceled active off-zero clock, live star third | $13624=2^3\cdot13\cdot131$ |

These are simpler certificates than the resultant norms and have exactly the same nonpaid prime support. The identities themselves hold over **all commutative rings**. The typed scalar consequences use an **integral domain** and the stated distinctness of the Gauss roots, because the divided differences are extracted by multiplying by, and then canceling, nonzero root differences. Both native exclusion corollaries assume characteristic zero but do not require a field or an ordering. No unconditional inference for arbitrary rings with zero divisors is made.

For the silent chart, the normalized reflected gap satisfies $y-x=xv$ and $-2+v+4v^2-v^3=0$. The resulting gate is the polynomial $-2x^3+(y-x)x^2+4x(y-x)^2-(y-x)^3$. The two live no-active-clock charts use three pairwise distinct roots of $L$ related by $s=2y-x$ or $s=4x-y$. In the canceled-clock chart, $x,y$ are distinct Gauss nodes, $v^2-2v-1=0$, and $y(1+v)=x(1+2v)$ or $x(3-v)$. The latter two identities use homogeneous clearing of the **cubic divided difference**, with no division by $x$ or $1+v$ on the Lean side.

The native source is `RKCert.Research.SDIRKEightFourZeroNativeRear`. The attached `generate_identities.py` reproduces the five identity statements with SymPy 1.14 using the univariate extended Euclidean algorithm over a degree-four or degree-two rational number field. It clears all rational coefficients and verifies each expanded exact integer identity locally. Regeneration is optional: the five Lean proofs are `ring` checks over an arbitrary commutative ring, and the two characteristic-zero endpoint theorems have the supplied stock Lean/Mathlib 4.36.0 axiom audit. No numerical stage bound changes.
