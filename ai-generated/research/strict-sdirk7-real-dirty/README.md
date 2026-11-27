# Exact real-algebraic cubic dirt at nine strict SDIRK7 stages

> **Follow-up:** The [exact primitive-field calculation](../strict-sdirk7-dirty-number-field/README.md) identifies the two isolated points as embeddings of a single degree-324 field. This original construction did not determine the field or its other embedding.

The reflection branch of the [unpaid three-helper chart](../strict-sdirk7-unpaid-head/README.md)
has a second, **real-algebraic** point giving a strict nine-stage
tableau of exact order seven. The first three output weights and
the third quadratic defect are zero, the six tail clocks are
distinct, their weights are nonzero, and there is an actual visible
cubic defect. The third helper axis is genuinely unpaid. This
changes neither the rational stage bound nor the previously known
real nine-stage upper bound; it separates the clean and dirty
architectures over characteristic zero.

This is **not** an identification of the isolated real solution
with a conjugate of the separate 19-adic point. It proves an exact
real-algebraic witness with its own coefficient field, whose degree
is not determined here. It gives neither a rational witness nor a
real-place assertion for the specific 19-adic field.

## Exact isolation

Use the same five equations as in the [unpaid-head derivation](../strict-sdirk7-unpaid-head/README.md#a-native-finite-witness-and-five-equation-lift),
with common diagonal \(\gamma=1/z\), reflected terminal clocks
\(4,0,1\), and normalized first tap \(t=1/2\). In the variable
order \((z,a,b_*,c_*,h)\), the rational center is the literal
terminating-decimal vector in [check-real-box.py](check-real-box.py).
Its leading decimals are

\[
(-13.47182912965383,\ -11.89349984962544,\ -6.20023810492232,\
 4.67852421480146,\ -0.83745225553178).
\]

The certificate uses the closed infinity-norm ball of radius
\(r=10^{-30}\) around the **full** rational center \(X_0\);
the shortened display above is not the input certificate.

Let \(F\) be the literal five rational functions. The script
encloses their values and first derivatives on the whole ball.
Every interval endpoint is an integer divided by \(10^{90}\);
integer floor/ceiling is used outward on every product and quotient.
The sum, product, power and quotient rules then propagate derivative
enclosures. Any interval denominator that could meet zero causes
the check to fail. No floating-point operation or approximate CAS
result is used in this replay.

Let \(Y\) be the exact rational inverse of the matrix of centers
of the derivative enclosures at the single point \(X_0\). The
certificate checks
\[
 \sup_{X\in B}\|I-YJ_F(X)\|_\infty < 10^{-18},
 \qquad \|YF(X_0)\|_\infty < 10^{-48}.
\]
Consequently \(X\mapsto X-YF(X)\) is a strict contraction mapping
\(B\) strictly into itself. The unique fixed point in \(B\) has
\(F(X)=0\), because \(Y\) is nonsingular by its construction;
\(J_F\) is nonsingular there by the same derivative bound.
This is a rational interval proof of existence and local uniqueness
of an exact real vector, not an inference from small residuals.
The rational equation denominators are nonzero throughout \(B\).

Clearing the denominators at this zero preserves the invertible
Jacobian. In characteristic zero, an invertible Jacobian for five
polynomial equations in these five unknowns forces their field
to have transcendence degree zero. Indeed, differentiating the
equations under any rational derivation forces every coordinate
derivative to vanish. If the field had positive transcendence
degree, a nonzero derivation on a transcendence basis would
extend across its finite separable algebraic remainder. Thus all
coordinates, and the rational assembly formulas, are real algebraic.

## Unit, visibility, and exact-order checks

The certificate verifies a strict lower bound \(10^{-5}\) on the
absolute value of every required nonconstant pivot throughout the
ball: \(z\), all tail clock gaps and gaps from \(h\), all six
weights, \(D_3,v_3\), the denominator defining \(\eta\),
\(q(z-a)\), the head \(3\times3\) determinant, and the terminal
\(4\times4\) reverse determinant. Shorter reverse solves are
Vandermonde solves at distinct sites with nonzero weights.
The signs need not be positive for a division in the real
field. In fact \(z,D_3,q(z-a)\) and the terminal reverse
determinant are negative, whereas \(v_3\) and the head
determinant are positive. One of the six weights is negative.

The [unit-pivot assembly and graded-flag proof](../strict-sdirk7-unpaid-head/README.md#why-the-five-equations-suffice-over-a-unit-pivot-ring)
therefore applies to the isolated zero over its own real number
field. It proves all rooted conditions through order seven exactly:
the five equations give the uniform quadrature, reverse reads, and
a rank-one dirty cubic column; those reads, their degree budgets,
and the paid square give the complete graded order check.
For genuine visibility, the certificate separately checks both
\((A'g)_3\) and \(v_a\) are positive and \(v_3\ne0\).
The assembled tail value \((A'g)_3 v_a/v_3\) is then nonzero,
and \(D_3\ne0\) excludes payment of the third axis.
The physical eighth-order bush residual from one is
strictly positive, approximately \(0.007915262488753348\).
Hence the order is exactly seven.

## Replay and independent cross-check

From this directory, run:

    python3 check-real-box.py
    python3 check-reduced-box.py

Both use the standard library only. The second script reduces to
three parameters \(z,c_*,s=a+b_*\): it eliminates \(p=ab_*\)
linearly from \(I(P)=0\), recovers the distinct \(a,b_*\) by a
directed-rounding square root, and eliminates \(h\) linearly
from the reflected third reverse condition. It certifies a
second contraction in this reduced chart, sends the full root
into the first certified box, reconstructs the tableau with
interval Cramer solves, checks that all 85 independent rooted
residual enclosures contain zero with absolute bound \(10^{-18}\),
and verifies the eighth-bush sign again. Residual enclosures
are consistency checks, not an exact-order proof; exactness
uses the symbolic unit-pivot and graded-flag argument.

The interval and contraction proofs here are mathematical with
exact replay; no claim is made that the real-root certificate
or symbolic assembly has already been formalized in Lean. The
separate finite-field witness and rational structural gate in
the neighboring packet retain their original native status.
