# The live terminal polynomial in the dispersed rank-four chart

Here \(E_q\) is the actual stage-column span through trees with \(q+1\) vertices, and \(V_m\) is the normalized defect span through size \(m\) (\(V_m=\mathrm{zeroSpace}(A,m-1)\)). The clock is \(\boldsymbol c=A\boldsymbol1\) and its diagonal matrix is \(C\).

Suppose \(A\) is strict with 11 stages, the method has order eight, and \(\dim V_5=4\). The [Lean module](../../lean/RKCert/ReviewedNative/ERK8RankFourTerminalKernel.lean) proves that the first reflected row vanishes, the second reverse space equals \(E_4^\perp\), and
\[
             \dim E_5=10,\qquad E_5^\perp=\operatorname{span}(\boldsymbol J_1).
\]
These are field-level statements and do not require ordered coefficients. If the terminal row is live, the module also proves \(c_{11}=1\), \(\boldsymbol e_{11}\in E_4\), and \(v_{11}=0\) for every \(\boldsymbol v\in V_4\). The rational specialization includes the following literal terminal polynomial:
\[
  K(X)=20X(2X-1)(7X^2-7X+1),\qquad
  \boldsymbol e_{11}-b_{11}K(\boldsymbol c)\in V_5 .
\]
Consequently every nonterminal pure rational row has clock \(0\) or \(1/2\), and a terminal pure through size five has exactly \(b_{11}=1/20\). These consequences are also native theorems. The [new universal witness](README.md) has \(b_{11}=7/80\), so the dispersed terminal defect is necessary for its chosen scalar rule.

The proofs are kernel checked on Lean 4.36.0 using standard axioms only. Run **lake build RKCert.ReviewedNative.ERK8RankFourTerminalKernel**. The universal construction certificate is independent of this module.

## Proof mechanism

The even midpoint budget gives \(\boldsymbol J_0=0\), \(\dim E_4=9\), and exact saturation of the two-dimensional reverse space. Reverse chronology forces this whole space to vanish at the terminal coordinate. Its annihilator therefore contains the physical coordinate \(\boldsymbol e_{11}\); the terminal column of a strict tableau is zero, and the first reverse balance forces \(c_{11}=1\). Paid rooted products of a size-four defect and a size-five stage column show
\[
 \boldsymbol b\odot V_4\subseteq E_4^\perp ,
\]
so a live terminal row is exact through size four. If \(E_5=E_4\), invariance of \(E_4\) under \(A,C\) would make its annihilator reverse-invariant, contradicting the next reverse rank growth. The complementary dimension budget at \(E_5\) then gives exact ranks 10 and 1.

By the normalized forward decomposition, \(\boldsymbol e_{11}\) is a degree-four clock polynomial plus an element of \(V_5\). Evaluating at the explicit origin \(c_1=0\) removes the constant; the four paid output moments give a nonsingular shifted Cauchy system. Its four right-hand sides are \(b_{11}\), because the terminal clock is one. One checks exactly that \(\int_0^1 X^k K(X)\,dX=1\) for \(k=0,1,2,3\), so the polynomial is \(b_{11}K\). The quadratic factor has no rational root: clearing its denominator modulo seven first forces the denominator divisible by seven, then the numerator, a contradiction.

Two further mathematical consequences (not claimed native here) help select the dispersed order window. Since \(A\boldsymbol e_{11}=\boldsymbol0\), closure under unary integration and clock multiplication give the two degree-five polynomial defects
\[
 (1-\boldsymbol c)K(\boldsymbol c)\in V_6,\qquad
 I K(\boldsymbol c)\in V_6,\quad
 I K(X)=56X^5-105X^4+60X^3-10X^2 .
\]
Here \(I\) is zero-constant integration; the primitive defect between \(A K(\boldsymbol c)\) and \(I K(\boldsymbol c)\) is itself paid in \(V_6\). These two polynomials are independent. With six distinct clock values their evaluated span exhausts the polynomial intersection of \(V_6\): the explicit origin removes the constant and the three output probes remove three of the five remaining coordinates. Hence \(\dim V_6=6\).

## The quiet-head rank-three option is constrained

Suppose additionally that exactly seven physical weights are nonzero, occupying seven distinct scalar clocks including the origin and terminal. Then every size-four defect vanishes in every weighted row: its weighted vector annihilates powers through degree four, and vanishes already at the two endpoints, leaving five distinct sites and a nonsingular Vandermonde.

If \(\dim V_4=3\), it follows that \(V_4\) is supported on the four inactive rows. The terminal polynomial forces a nonzero size-five restriction on the weighted rows (only one nonterminal nonzero rational pure clock is possible), so the kernel of that restriction from \(V_5\) is precisely \(V_4\). This kernel is \(C\)-invariant, since \(CV_4\subset V_5\) and \(CV_4\) still vanishes on the weighted rows. Its annihilator on the four inactive rows is a line carried at one clock.

That line cannot have zero aggregate mass or be at clock zero. If it did, every positive-degree clock polynomial masked to the four inactive rows would lie in \(V_4\). On the weighted rows, the restrictions of \(AV_4\) and the cubic primitive defect then lie on the same size-five leakage line, say \(\boldsymbol\nu\). Hence the weighted-to-weighted portion of the physical row evaluates any polynomial \(G\) with zero constant and degree at most three as \(I G(c_i)+\mu_G\nu_i\), with a scalar \(\mu_G\) independent of the receiving row. Let \(h\ne0\) be the first nonzero weighted clock. The test \(G=X\) shows \(\nu_h\ne0\). At the first new nonzero weighted clock \(x\), the polynomials \(X(X-h)\) and \(X^2(X-h)\) both vanish on all previous weighted rows. The two tests force
\[
 \frac{x^2(3h-2x)}{h^3}
 =\frac{x^3(4h-3x)}{h^4},
\]
so \(x=h\), a contradiction. In particular a rank-three \(V_4\) of this type needs a substantive nonzero-mass repeated inactive clock; four distinct inactive clocks would make the annihilator a singleton and \(V_4\) a coordinate space. A coordinate \(V_4\) rank-three space likewise admits the same one-line argument even without assuming this seven-site weighted census.

These restrictions explain the choice \(V_4\) rank two in the new universal tableau. Its rank-four \(V_5\) is genuinely dispersed and does not contradict any earlier small-support exclusion.
