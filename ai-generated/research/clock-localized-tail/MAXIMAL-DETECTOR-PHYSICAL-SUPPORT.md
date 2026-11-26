# A maximal clock detector cannot consume its last available row

Use the setting of the [maximal-delay theorem](MAXIMAL-ODD-CLOCK-DELAY.md), for a hypothetical order-\(2d+1\) explicit method with \(3d+1\) stages and \(d\ge7\). Assume \(\epsilon=1,\delta=d\). Let \(\boldsymbol\lambda\coloneqq\mathbf h_1=\mathbf bA-\mathbf b(I-C)\), let \(S\) be its actual physical support, and let \(M\) be its complement. The reverse chart states
\[
 E_d^\perp=\boldsymbol\lambda P_{\le d-1}(C),\qquad
 f_i=P_{\mathbf f}(c_i)\quad(i\in S,\ \mathbf f\in E_{d-1}),
 \qquad \deg P_{\mathbf f}\le d-1 .
\]
Here the actual \(\boldsymbol\lambda\)-supported stage profiles form the chart; \(P_{\mathbf f}\) is initially not assumed to be the exact model.

**Claim.** If \(d\ge7\), the only possible support size is \(|S|=2d+1\). All its detector clocks are distinct, its weights are proportional to their nonzero barycentric weights, and its \(d\) offsupport rows have a \((d-1)\)-dimensional measured restriction kernel in \(E_{d-1}\). In particular the case where all clock aggregates of \(\boldsymbol\lambda\) vanish is impossible. This restricts a single class of maximal-delay tableaux; it does not exclude the other maximal-delay alternatives or improve an unrestricted stage bound by itself.

## The physical support cost

The detector has at least \(d+1\) distinct supported clocks. Otherwise its exact rank-\(d\) clock orbit through degree \(d-1\) would already be clock-invariant, making its annihilator \(E_d\) clock-invariant, contrary to \(\delta=d\). The restriction of \(E_{d-1}\) to the support \(S\) has rank exactly \(d\): at most \(d\) by the chart, at least \(d\) from evaluations of the literal clock polynomials. The pure dimensions through levels \(d-1,d-2\) are exactly \(d-1,d-2\). Indeed the ordinary size-six floor gives \(\dim F_5\ge5\), all increments through \(d\) are at least one, and \(\dim F_d=d\). The indices \(d-2,d-1\) are both at least five when \(d\ge7\).

In particular
\[
 \dim E_{d-1}=2d-1,\qquad
 \dim\ker(\operatorname{res}_S|_{E_{d-1}})=d-1,\qquad
 |M|\ge d-1,\quad |S|\le2d+2.                                    \tag{1}
\]
If all clock aggregates of \(\boldsymbol\lambda\) are zero, every one of its at least \(d+1\) clock groups must contain at least two physical support rows, giving \(|S|=2d+2\). Otherwise the exact zero moments \(\boldsymbol\lambda C^a\cdot\mathbf1=0\) through \(a=2d-1\) require at least \(2d+1\) nonzero clock aggregates by Vandermonde. It remains to exclude \(|S|=2d+2\) irrespective of its aggregate pattern.

## With only \(d-1\) offsupport rows, every detector stage is clean

At \(|S|=2d+2\), its complement has exactly \(d-1\) rows, and (1) identifies the actual restriction kernel with the entire coordinate subspace supported there. Thus for \(i\in M\), the coordinate direction \(\mathbf e_i\) is an actual member of \(E_{d-1}\).

In fact every such direction is pure and \(b_i=0\). If its degree-\((d-1)\) exact model is \(P\), the paid word tests give
\[
       \int_0^1 X^aP(X)\,dX=b_i c_i^a\qquad(0\le a\le d+1).
\]
Subtracting the tests at \(a+1\) and \(a\) weighted by \(c_i\), the polynomial \((X-c_i)P\) is orthogonal to all polynomials through degree \(d\). It also has degree at most \(d\), so the ordinary paid moment Gram gives \(P=0\), and then \(b_i=0\). The only denominator budget here is \(p!\). It follows that, for every \(\mathbf f\in E_{d-1}\), the difference \(\mathbf f-P_{\mathbf f}(\mathbf c)\) is pure: it is supported on \(M\), and each coordinate direction there has just been proved pure. Hence \(P_{\mathbf f}\) is the exact model. Every stage in \(S\) therefore reads all profiles through degree \(d-1\) as their exact values at its own clock. In particular \(F_{d-2}\) is supported on \(M\).

## A one-dimensional incoming feed cannot produce the second nonzero clean clock

For every receiver in \(S\), its actual incoming row restricted to \(M\) annihilates \(F_{d-2}\), since \(A F_{d-2}\subseteq F_{d-1}\), whose coordinates on \(S\) are zero. As \(\dim F_{d-2}=d-2\) and \(|M|=d-1\), all those restrictions belong to the same one-dimensional space of rows on \(M\). The exact polynomial primitive identity at every such receiver reads
\[
                     \bigl(A P(\mathbf c)\bigr)_i
                         =\int_0^{c_i} P(X)\,dX
                  \qquad(\deg P\le d-2,\ i\in S).
\]

Let \(\theta\) be the first nonzero clock in \(S\) by physical chronology. Every earlier receiver in \(S\) has clock zero, so on polynomials \(P\) with \(P(0)=0\) the first incoming read on \(M\) equals the nonzero primitive functional up to \(\theta\); \(P=X\) shows it is nonzero. Therefore it spans the common line of actual \(M\) feeds. Let \(y\) be the first further nonzero clock in \(S\) distinct from \(\theta\). Such a clock exists because \(S\) has at least \(d+1\) distinct labels. Before it all clocks of \(S\) are \(0\) or \(\theta\). For the two inputs \(P_1=X(X-\theta)\) and \(P_2=X^2(X-\theta)\), the contribution from the earlier \(S\) rows is zero. The incoming reads of both polynomials at \(y\) must consequently be the same scalar multiple of their incoming reads at \(\theta\).

Writing \(z=y/\theta\), the two ratios of the exact primitives are \(z^2(3-2z)\) and \(z^3(4-3z)\). Their equality gives \(3z^2(z-1)^2=0\); the field is paid and \(y\ne0\), so \(y=\theta\), a contradiction. This rules out \(|S|=2d+2\).

Thus the remaining configuration has \(|S|=2d+1\), each support row at a distinct clock. The first \(2d\) zero aggregate moments make the detector row the unique barycentric line on that grid: if \(N(X)\coloneqq\prod_{i\in S}(X-c_i)\), then \(\lambda_i=\kappa/N'(c_i)\) for some \(\kappa\ne0\). This is the Lagrange leading-coefficient identity through the stated zero degrees. The \(d\) offsupport rows \(M\) carry the measured hyperplane \(\ker(\operatorname{res}_S|_{E_{d-1}})\) of dimension \(d-1\), not necessarily the entire coordinate space there. One cannot conclude that all its individual coordinate directions belong to \(E_{d-1}\), are pure, or that the detector chart is already exact on this surviving configuration.

For \(d=6\), the proof also applies if \(\dim F_4=4\); without that extra hypothesis the available argument gives a two-dimensional common \(M\)-feed rather than one and does not remove this case. All results are source arguments through paid fields, with no runtime or Lean acceptance asserted.
