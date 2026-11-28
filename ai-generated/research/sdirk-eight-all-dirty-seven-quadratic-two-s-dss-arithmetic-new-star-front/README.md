# Two-singleton front star versus rear D,S,S arithmetic, with a new terminal clock

Let a strict ten-stage SDIRK tableau have ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven different clocks, and exactly one singleton physical endpoint. Orient from that singleton. Suppose the front has two singleton labels and one double, and its true third-row phase is a **star**. It cannot face genuine D,S,S arithmetic at the doubled end. The [reused-terminal result](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-reuse/README.md) covers when the front double reuses the terminal clock; the present packet excludes the terminal-new case. Both front literal star orders and all coefficient extensions in characteristic zero are covered. This does not decide the forward arithmetic phases with a new terminal, nor the opposite one-extra-D opening, and the general 10–11 stage interval is unchanged.

## The paid affine factor recovers the quadratic graph

Normalize the diagonal to one and write \(y=x-1,\ m=1/(2\gamma),\ H=2(m-1),\ t=y-H/2\). The first singleton label and defect are \(0,1/2\), the genuine terminal double is at \(H\ne0\), the later front D is at \(d\ne H\), and the later front S is at \(s=2-d\) in the literal star. Their known defects \(f_d,f_s\) both equal \(\kappa(d)/2\), \(\kappa(z)=1+2z-z^2\). This pair data comes by applying the true star formula separately to either physical order, using \(\kappa(2-d)=\kappa(d)\); no row permutation of a proposed tableau is used. The singleton front first-departure guard rules out its actual gap of two. The rear D,S,S arithmetic gap \(v\) gives original S labels \(p=H-v,\ q=H-2v\). All four singleton labels \(0,s,p,q\) are used, distinct, and nonzero-defect.

By the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), \(\mathcal Q=L_3-F_*L_4\) is proportional to \(P R\), where \(R\) is the genuinely quadratic singleton graph, \(P\) has the three distinct doubled roots, and \(F_*\) is affine nonconstant. The monic centered Legendre modes are evaluated at \(t=y-H/2\). The values \(L_4(H),L_4(d)\) cannot vanish, by coprimality at roots of \(\mathcal Q\). Fit \(F_*\) from the actual D anchor values \(L_3/L_4\) at \(H,d\) and form
\[
 M_3(y)=\mathcal Q(y)/[(y-H)(y-d)] .
\]
The quotient is exact. If \(e\) is the third D, this cubic equals \(L R\) with \(L\) affine of nonzero slope, proportional to \(y-e\). The two actual front singleton measurements fix **both** affine coefficients:
\[
 L=l_0+l_1y,\qquad l_0=2M_3(0),\quad l_1=(M_3(s)/f_s-l_0)/s .
\]
Here \(s,f_s\ne0\) and \(l_1\ne0\) is a true graph-factor property, not a conjectured pivot. The clock satisfies \(e=-l_0/l_1\). Write
\[
 R=\tfrac12+a y+b y(y-s),\qquad a=(f_s-\tfrac12)/s,\qquad
 b=[y^3]M_3/l_1 .
\]
This determines the actual nonzero curvature by matching the leading coefficient. The measured constant and value at \(s\) already agree with \(M_3=L R\), so the remaining necessary coefficient gate is
\[
          E = [y^2]M_3\,l_1-l_1^2 a-[y^3]M_3(l_0-l_1 s)=0 .
\]
There is no assumption that \(a\ne0\), or that \(R\) has distinct roots, splits in the ground field, or has no overlap with D. The nonzero curvature and genuine slope follow from the quadratic graph, and no division by \(R\) at a D label is made. The [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids centered and antipodal D labels, including \(e\); these guards are used only where asserted.

## Scalar rear ratio, nodal determinant, and actual pair fits

Put \(\kappa=1+2v-v^2,\ D=-2+v+4v^2-v^3,\ \widehat q=D-v(v-2)(3v-2)\). The two actual rear normalized S residuals are \(\kappa/2,\kappa\widehat q/(2D)\). The true rear arithmetic guards are nonzero \(v,\kappa,D,\widehat q,3v-2\). Rear \(v=2\) is not excluded solely by that gap, as the rear first label is a double. Using the common true reverse normalization \(\lambda\ne0\), set \(\mu=\kappa\lambda=2R(p)\). The ratio \(D R(q)=\widehat q R(p)\) gives the cubic (or degenerate lower-degree) necessity
\[
         \mathcal R=D\bigl(b(2H-3v-s)+a\bigr)-(v-2)(3v-2)R(p)=0.
\]
This equality follows by cancelling only the true nonzero \(v\) from the difference of the two graph values. No higher coefficient of the ratio needs to be invertible.

Write \(W=R/b\) monic and \(S_4=y(y-s)(y-p)(y-q)\). The true singleton quartic \(\mathcal H=L_4-RC=h_4S_4\), \(C=A_2+B R\), has \(h_4\ne0\). If \(L_4\bmod W=a_0+a_1y\), \(S_4\bmod W=z_0+z_1y\), then
\[
                          \mathcal N=a_0 z_1-a_1 z_0=0.
\]
The quadratic remainders keep repeated roots; neither component is used as a pivot. \(\mathcal N\) has degree at most two in \(v\).

There is also an exact \(C\)-fit using the three actually measured S readings \(0,s,p\). Set \(Z=\mu C\), \(\Omega=s p(p-s)\ne0\), and use the quadratic \(\widehat Z=\Omega Z\) fixed by these values:
\[
\begin{split}
 \widehat Z(y)={}&2\mu L_4(0)(p-s)(y-s)(y-p)\\
 &-\mu L_4(s)p\, y(y-p)/f_s+
                 2D L_4(p)s\, y(y-s)/\widehat q.
\end{split}
\]
Thus the actual remaining S at \(q\) enforces
\[
 \mathcal X=\widehat q\,\widehat Z(q)-2D\Omega L_4(q)=0 .
\]
At the two observed D labels the known defects are \(f_d\) and \(\mu/(2\kappa)\). Put \(P_d=f_d(f_d-R(d))\ne0\) by the genuine off-graph double, and \(J_d=\mu\Omega L_4(d)-f_d\widehat Z(d)\). Using the front D equation \(J_d=\mu\Omega B P_d\) together with the actual terminal D equation gives the necessary row
\[
 \mathcal Y=P_d\bigl(4\kappa^2\Omega L_4(H)-2\kappa\widehat Z(H)\bigr)
                       -J_d(\mu-2\kappa R(H))=0 .
\]
This clears only nonzero phase/scale denominators and uses no inversion of an unknown fit rank, including when a special row loses leading terms. The two actual D values need not agree with each other.

## Exact projections and fixed places

Use \(E,\mathcal R,\mathcal N,\mathcal X,\mathcal Y\) also for their guarded integer numerators. The verifier checks all nonconstant denominators against true clock and phase guards, anchor Legendre values, \(M_3(0)\), and the measured affine-factor slope; it does not discard any factor just because of a specialized leading coefficient. Let \(\Pi=\operatorname{Res}_v(\mathcal R,\mathcal N)\) after stripping only actual guards involving \(H,d\). Its degree pair in \((H,d)\) is \((84,43)\). The next resultant \(\operatorname{Res}_d(E,\Pi)\), after stripping only true \(H\)-guards, has degree 772 and the irreducible factor-degree/multiplicity list
\[
       (1,2),(2,3),(4,1),(6,24),(9,32),(12,9),(54,1),(166,1).
\]
These are necessary projections, not assumed to exhibit actual paid fits.

The verifier uses each short exact certificate shown below, not a prime sweep. "Direct" means use the full simultaneous residue equations. "Cleared anchor" means first strip actual \(H,d\)-guards algebraically from \(E\) over the irreducible \(H\)-field, and normalize the surviving \(d\) polynomial to monic. This is not dismissal of a forbidden residue after reducing.

| \(H\) factor degree, multiplicity | Certificate | Prime | \(H\) residue | \(d\) test at that residue |
| --- | --- | ---: | ---: | --- |
| 1, 2 | direct | 17 | 2 | \(0\) |
| 2, 3 | direct | 11 | 5 | \(0\) |
| 4, 1 | cleared anchor | 23 | 0 | unit anchor gcd |
| 6, 24 | cleared anchor | 19 | 16 | unit anchor gcd |
| 9, 32 | cleared anchor | 13 | 10 | unit anchor gcd |
| 12, 9 | direct | 101 | 24 | \(1,23,58\) |
| 54, 1 | direct | 43 | 32 | \(18\) |
| 166, 1 | direct | 11 | 4 | \(2\) |

In each row the rational \(H\)-factor is irreducible and the chosen residue root is simple with unit leading coefficient. Hensel gives an embedding of the abstract \(H\)-field into \(\mathbb Q_p\) at that root. In a direct row the true \(d\)-degree of \(E\) after specializing to the abstract \(H\)-field is preserved upon reduction, and is positive. Thus a putative \(d\) is algebraic and integral at the place. In the cleared-anchor rows the retained monic \(d\)-polynomials are of degrees 6, 6, 3 respectively, and their field coefficients are exactly checked integral at the selected \(H\) root. Any actual \(d\) still solves that trimmed polynomial because every removed factor was supported by an original nonzero guard. The unit gcd of its reduction with the reduction of \(\Pi\) proves no such \(d\) exists, without requiring either polynomial to split.

In a direct row the \(d\)-values listed are **all** roots of the reduced \(d\)-gcd of \(E,\Pi\), with total multiplicity checked against its full degree. At each \(d\) at least one of the four \(v\)-rows retains its full positive degree, so \(v\) is algebraic and integral. The simultaneous gcd of the four reduced equations \(\mathcal R,\mathcal N,\mathcal X,\mathcal Y\) in \(v\) is a unit. This checks every possible residue component, including ones where an original guard happens to reduce to zero. There is no inversion of such a residue guard, as all four rows are already integer necessary equations of any actual mesh. Thus the Hensel transfer covers every putative characteristic-zero solution, including nonsplit coefficients. It asserts no finite-characteristic census.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_front_star.py` with SymPy 1.14 and python-flint 0.8. It regenerates the exact projections with the original physical guards, factors them and checks the fixed places. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewStarFront.lean) verifies the affine-factor coefficient and nodal scalar identities. The rooted-order ingress, exact projections, and local-field transfer remain a mathematical proof with independent exact replay, not a full native Lean theorem.
