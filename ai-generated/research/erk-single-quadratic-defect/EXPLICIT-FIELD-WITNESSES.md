# Literal six-stage witnesses for the restricted order-five field separation

This supplements the exact scope and necessity proof in [the field classification](ORDER-FIVE-MINIMAL-DEFECT-FIELD-THRESHOLD.md). The setting is ordinary explicit order five with at most six stages, exactly one nonzero stage-order-two defect coordinate, and exactly three actual pure directions through size five. No other order-five method classes or global minima are being compared.

## The conjugate complex pair, also defined in paid positive characteristic

Let \(K\) be any field with \(5!\) invertible and choose \(\delta\in K\) with \(\delta^2=-15\). Put
\[
                        x\coloneqq(15+\delta)/12 .
\]
The two choices of \(\delta\) give the complex conjugate pair over \(\mathbb C\). They satisfy \(6x^2-15x+10=0\) and none of \(x,1-x,2x-1\) vanishes: the corresponding polynomial evaluations at \(0,1,1/2\) are \(10,1,4\), up to the harmless displayed scale, and are all nonzero. More explicitly the evaluation at \(1/2\) is \(4\). The constants and factors divided out below are therefore units.

Give the six successive predecessor rows of the *physical* coefficient matrix by dividing each of the following rows by \(x\):
\[
 (),\quad (1/4),\quad (0,1/2),\quad (1,-2,2),\quad
 (1,0,4,1)/6,\quad (h_1,h_2,h_3,h_4,h_5),
\]
where
\[
 \begin{aligned}
 h_2&\coloneqq4x^2(1-x),&
 h_3&\coloneqq(2/3)x^2(2x-1),\\
 h_4&\coloneqq x^2(2x-1)(7/6-x),&
 h_5&\coloneqq x^2(1-x)(1-2x),\\
 h_1&\coloneqq x-h_2-h_3-h_4-h_5 .
 \end{aligned}
\]
The actual output vector (no further scaling) is
\[
 \begin{aligned}
 \mathbf b&\coloneqq(\alpha,0,-\lambda\beta,-\lambda\gamma,\eta,\lambda),\\
 \beta&\coloneqq16x^2(1-x)^2,&
 \gamma&\coloneqq2x^2(1-x)(1-2x),&
 \lambda&\coloneqq\frac{x-1}{2(2x-1)},\\
 \eta&\coloneqq x/2-\lambda(x-\beta/2-\gamma),&
 \alpha&\coloneqq1-\eta-\lambda(1-\beta-\gamma).
 \end{aligned}
\]
This specifies both members of the pair using field arithmetic alone.

In the normalized (before division by \(x\)) units the exact model reads are \(P(0),P(1),P(x)-\beta P(1/2)-\gamma P(1)\), implemented by \(E_1,E_5,R\) respectively. The earlier rooted calculation proves those are exact through size five. The normalized mean \(x^{-1}I_x\) belongs to their span because the two common model-kernel primitives vanish at \(x\) by the quadratic relation. The coefficient of the third read is its mean on the cardinal polynomial at \(x\) among the four nodes \(0,1/2,1,x\). Its numerator simplifies to
\[
       x^{-1}I_x[X(X-1/2)(X-1)]=x(x-1)^2/4,
\]
giving the displayed \(\lambda\). Testing \(X\) and 1 gives \(\eta,\alpha\). This proves the actual output weights, not just existence of a linear functional on the model. Scaling the matrix gives the physical order-five equations by rooted homogeneity. On the first six raw coordinates the pure size-five space is exactly \(\operatorname{span}(\mathbf q,\mathbf f,C\mathbf f)\): its three stated pivots are nonzero, and the established tree expansions put every pure difference there. The cross-order minimum-defect theorem excludes order six for this same six-row class.

## A literal example in characteristic 17

In \(\mathbb F_{17}\), take \(\delta=-6\), so \(\delta^2=2=-15\) and \(x=5\). The actual chronological predecessor rows above are
\[
           (),\quad (6),\quad (0,12),\quad (7,3,14),\quad
               (4,0,16,4),\quad (1,5,13,6,10),
\]
and the output is \((5,0,2,8,16,4)\). For example \(\beta=8,\gamma=15,\lambda=4,\eta=16,\alpha=5\) in that field. The root, matrix, and output are therefore all nonempty in a paid positive characteristic, unlike the branch over an ordered field. The proof is not restricted to this prime: it only requires \(5!\) invertible and \(-15\) square. Necessity proved the reverse implication over each such field, so fields of paid characteristic for which \(-15\) is nonsquare fail the same restricted stratum.

The formulas also exist in the paid algebra \(\mathbb Z[1/5!,\delta]/(\delta^2+15)\). The product of the two conjugate values of \(x\) is \(5/3\), of \(1-x\) is \(1/6\), and of \(2x-1\) is \(8/3\), all units. Thus no extra division is concealed by the field formulas for \(\mathbf b\). Under any nonzero commutative base change from this algebra the order-five identities remain true. If it also satisfied order six, a residue field would give order six in the excluded six-stage single-defect case.
