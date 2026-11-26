# When a six-row ordinary order-five seed can have only three pure defects

Let \(A\) be an explicit tableau over a field with \(5!\) invertible. Seek ordinary order at least five on at most six physical rows, exactly one nonzero component of the stage-order-two residual \(\mathbf q\), and \(\dim F_5=3\). This restricted seed class exists exactly when \(-15\) is a square in the coefficient field. In particular it cannot give a real (or ordered-field) replacement for the initial preparation considered here. This is not a lower stage bound for order five without the two defect assumptions.

## The necessary low-order shape

By the ordinary chronological no-plateau argument, \(\dim F_3=1,\dim F_4=2\). Merge duplicate rows and early origin profiles as in [the single-defect lower bound](SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md). Its entire first-four and fifth-row analysis through (3), including the case \(f_4=0\), used only the pure dimensions through size five. A fifth usable row therefore requires the ratio \(T=2N\), with fifth clock \(T\) and fifth coefficient on stage 2 unequal to the fourth coefficient. If there is no such fifth row, all output clocks still lie in \(\{0,N,T\}\), and only model evaluations at \(0\) survive on the first four rows: the pure directions \(\mathbf q,\mathbf f,C\mathbf f\) occupy every non-origin coordinate if \(f_4\ne0\), or \(\mathbf q,\mathbf f,A\mathbf f\) do if \(f_4=0\). This is incompatible with the nonzero first moment. Fewer than four usable rows are also impossible, since four unary extensions have zero derivative vector there and nonzero ordinary order-five target.

Normalize the clock \(T\) to one, so \(N=1/2\). Let \(a\ne0\) denote the scaled clock of stage 2. The exact ordinary terminal in this new coordinate is some \(s\ne0\), namely the reciprocal of the original clock \(T\). The exact output weights now reproduce the mean \(s^{-1}I_s\) on every polynomial through degree four. The only output-eligible clocks of the first five rows are \(0,1/2,1\), because the old stage-two weight is zero. If there is no novel sixth clock, the scalar hull of the original clocks \(0,T/2,T\) would be orthogonal to \(1,X\) for the uniform measure on \([0,1]\). Its mean is \((T-1)^2/4\), forcing \(T=1\). But then its first moment is \(-1/120\ne0\). The sixth row therefore has a clock \(x\notin\{0,1/2,1\}\) in the normalized coordinate. It can coincide with the old offending row's clock \(a\); the latter's zero output weight does not affect the argument.

The old ratio proof, or rescaling its first-four moment identities, gives
\[
 \begin{aligned}
  \mathbf q&=-a^2\mathbf e_2/2,\
  \mathbf u&=(2a/3)\mathbf q+(a^2-a/3)\mathbf f,\
  \mathbf v&=(a^2/2)\mathbf q+[a^3+(a/4)(C-I)]\mathbf f,
 \end{aligned}
]
where \(\mathbf f=A\mathbf e_2\), \(\mathbf u=A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3\), and \(\mathbf v=A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4\). On the first five donor coordinates the cubic clock data satisfy
\[
 \mathbf c^{\odot3}=(3/2)\mathbf c^{\odot2}-\mathbf c/2
                         +a(a-1/2)(a-1)\mathbf e_2 .
\]
The sixth row necessarily reads \(\mathbf c\) as \(x^2/2\). Its second and third clock moments in the displayed identities therefore force
\[
                         f_6=x^2(1-x)/a .
\]
Indeed the cubic relation subtracts to \(-x^2(x-1)^2/4=(a/4)(x-1)f_6\), and \(x\ne1\).

## The exact field obstruction

The pure size-five space is spanned by \(\mathbf q,\mathbf f,C\mathbf f\). Its annihilator on these six raw coordinates has dimension three. A basis consists of the origin, a true endpoint read obtained by mixing the fourth and fifth raw coordinates with weights of sum one that kill \(\mathbf f\), and the read
\[
                 R\coloneqq E_6-\beta E_3-\gamma E_4,qquad
 \beta\coloneqq16x^2(1-x)^2,qquad
 \gamma\coloneqq2x^2(1-x)(1-2x).
\]
The latter annihilates the three vectors, using \(f_3=1/(8a)\), \(f_4=-1/(2a)\) and the displayed \(f_6\). Its model is \(P(x)-\beta P(1/2)-\gamma P(1)\). Among the three raw reads, the first is supported at 1, the endpoint is supported on 4 and 5, and the third has a nonzero sixth coordinate; they are independent. Therefore the exact ordinary mean must annihilate every polynomial of degree at most four in the common kernel of these three model reads.

Write \(v=2X-1\), \(d=2x-1\), and put
\[
    H\coloneqq(1-v^2)(v^2-\tfrac45 dv-\tfrac15),\qquad
    S\coloneqq\tfrac32(1-v^2)(1-dv).
\]
Both lie in that common kernel by direct substitution. They span it, because their degrees differ and the three reads are independent at the polynomial level (the four distinct site evaluations are independent in degree at most four). The lower primitive of \(H\) at \(s\) is \((d-(2s-1))(1-(2s-1)^2)^2/10\). Since \(s\ne0\), its vanishing leaves \(s=1\) or \(s=x\). The first gives \(I_1S=1\) and fails. The second gives
\[
                    I_xS=(d+1)^3(3d^2-9d+8)/16 .
\]
Because \(d\ne-1\), this vanishes exactly when \(3d^2-9d+8=0\), whose discriminant is \(-15\). In any ordered field the quadratic equals \(3(d-3/2)^2+5/4\) and does not vanish.

## Attainment over the indicated other fields

Conversely, let \(d\) be such a quadratic root and set \(x=(d+1)/2\). The paid arithmetic excludes \(x=0,1/2,1\) by evaluating the quadratic at \(-1,0,1\). Use the first six physical rows of the tunable grade-five chart, with this \(x\) in its sixth-row formula, a paid \(a\) (for example \(1/4\)), and the ordinary order-four output as the fifth row in the normalized units. These six physical rows have precisely the three pure size-five directions, all rooted defects are accounted for by the established coefficient calculation, and the same model read space applies. The average \(x^{-1}I_x\) kills both kernel polynomials. It is therefore a linear combination of the three published exact model reads, defining an actual raw output. Multiply every stage coefficient by \(1/x\) to put its physical terminal at one; leave the output weights unchanged. The output then satisfies all rooted ordinary conditions through order five by homogeneity, not merely the scalar tests. It cannot have order six, since the cross-order result forces five independent pure directions at size six, all supported on the five non-origin rows. An order-six output would then be supported only at the origin and would fail order two.

This comparison concerns a specific sparse forward defect budget. It does not demand negative discriminant in ordinary order-five methods that are allowed more actual pure directions or more than one stage-order-two defect.
