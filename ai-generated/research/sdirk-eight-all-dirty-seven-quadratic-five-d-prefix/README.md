# Quadratic seven-clock data with doubled endpoints cannot place five D rows in the two boundary triples

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with every literal quadratic residual nonzero and exactly seven distinct clocks. Its singleton graph \(R\) is genuinely quadratic. A physical clock label is D if it has two copies, S if it has one. This packet assumes the two actual endpoints are D, one genuine orientation begins **D,D,D**, and the other begins **D,D,S** or **D,S,D**. These are the cases with exactly five physical D rows in the two opening triples, because the endpoints are both D. They are all impossible, including a shared endpoint clock.

Together with the [two D,D,D exclusion](../sdirk-eight-all-dirty-seven-quadratic-two-triple-d/README.md), at least two of the six D rows must lie strictly between the first three and last three whenever both endpoints are D. No entry-weight sign, next-order assumption, or unconditional ten-stage exclusion is claimed.

## Actual D,D,D mesh and weighted overlap

Orient the tableau so its genuine forward prefix is D,D,D. Normalize its common diagonal to one, let \(\ell=1/\gamma=2m\), use \(t=x-m\), and put \(h=m-1\). Its two physical endpoint clocks are \(-h,h\). By the [odd-projection parity gate](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md), \(Q/B=L_3-\mu tL_4\), with \(\mu\ne0\) fixed by any nonzero D clock. Thus \(Q\) has paired nonzero roots and root zero, allowing repeated projection roots. If two nonzero D clock squares \(a^2,b^2\) are different, the parity condition gives
\[
 35a^2 b^2-21 m^2(a^2+b^2)+15m^4=0 .
\]
It is derived by cancelling the distinct squared roots, not assumed when they coincide.

Here are all forward D triples, in their actual order, from the exact arithmetic A and star S first-three gates:
- If \(h\ne0\), arithmetic is either \((-h,0,h)\) with gap \(u=h\), or \((-h,h,3h)\) with gap \(u=2h\).
- If \(h\ne0\), star has later labels \(h\) and \(2-3h\) in either order (gaps \(2h,\,2-2h\)). Retain the \(2-3h=0\) branch and allow it without the distinct-squared condition. Otherwise the squared roots \(h^2,(2-3h)^2\) are different because the three D labels are different, and the displayed relation applies.
- If \(h=0\), \(m=1\) and the ordered labels are \((0,u,2u)\) in arithmetic, or \((0,u,2-u)\) in star. In either genuine phase the latter two squared labels differ: equality with opposite sign would give \(u=0\) or \(2=0\), and equality with the same sign would duplicate a physical leading clock. Apply the squared-root condition to those two labels.

Let \(g_{\rm f}\) denote the known forward residual at each of these three D clocks. The exact first two normalized values are \(1/2,\kappa(u)/2\), \(\kappa(u)=1+2u-u^2\). The third is \(q_{\rm num}(u)/(2D(u))\) for arithmetic, where
\[
 D(u)=-2+u+4u^2-u^3,\qquad
 q_{\rm num}=(1+4u-4u^2)D+4u^2(3u-2);
\]
in star it is again \(\kappa(u)/2\). The forward labels and these formulas pay all known residuals; no other coefficient of the tableau is specified.

The genuine weighted mirror starts at original D label \(h\) with reverse residual \(1/2\). Its one other D label \(d\) is one of the other two labels; choose whether it is the second or the third reverse row, and choose the actual phase. Its normalized reflected clock is \(m-d\), so the reverse gap \(v\) is \(h-d\) if that D is second, \((h-d)/2\) if it is third and arithmetic, or \(2-h+d\) if it is third and star. This fixes the singleton original label \(\sigma\) and the two literal reversed normalized residuals \(g_{\rm r,D},g_{\rm r,S}\). Here \(g_{\rm orig}=\lambda g_{\rm rev}\) with nonzero \(\lambda\), not presumed one.

At each doubled label the product of its two residuals is \(-L_4(t)/B\). Each of \(h,d\) is occupied by one forward and one reverse D row. The two actual products therefore require a common nonzero value \(\beta=B\lambda\):
\[
 \beta=-\frac{L_4(h)}{g_{\rm f}(h)/2}
       =-\frac{L_4(d)}{g_{\rm f}(d)g_{\rm r,D}}.
\]
These are genuine stage equations, not aggregate weights. Their equality, the forward squared-root necessities wherever relevant, and all actual nonzero phase and distinct-clock guards give the exact univariate projections in the replay. The affine normalized Legendre leading slope must also be nonzero, and \(L_4\) may not vanish at a D label; these are included as guards. Every shared-clock \(h=0\) case is already excluded by this projection. The distinct endpoint projections yield only fourteen finite irreducible factors, with degrees \(10,7,4,1\). There is no free projected parameter. The code verifies that every denominator cleared follows from declared nonzero guards.

## Reconstructing the inverse scales and genuine rank

In each projected field reconstruct the three actual D labels and the observed reverse singleton. The exact monic graph polynomial \(W\) is obtained by dividing \(Q/B\) by its known D polynomial and making the quotient monic; write \(R=rW\). This does not divide by \(W\) at D labels, so common roots of \(R,P\) are allowed. Let \(T\) and \(A_0\) be the two degree-two interpolants of \(g_{\rm f}\) and \(L_4/g_{\rm f}\) on the three D labels. Since the quartic is \(U=L_4-g(A_2+B g)\), their true values give
\[
 A_2=A_0-\frac{\beta}{\lambda}T,\qquad B=\beta/\lambda.
\]
If \(W(\sigma)=0\), the observed singleton would have zero original residual, a contradiction (five projections). Otherwise its actual reversed residue fixes \(\nu=g_{\rm r,S}/W(\sigma)\ne0\), so \(r=\nu\lambda\). Substitution into \(H=L_4-R(A_2+B R)\) gives the **affine** formula
\[
 H=L_4+\beta\nu W T-\lambda\nu W(A_0+\beta\nu W).
\]
Thus the actual singleton equation \(H(\sigma)=0\) is affine in \(\lambda\).

An independent affine row comes from the [normalized trace](../sdirk-eight-all-dirty-seven-constant/README.md#the-trace-gate-and-its-normalization), \(2\sum1/g_i=\ell\sum b_i/g_i\). The scale \(\ell\) is necessary because the original output weights sum to one. For completeness, the following exact implementation of the [quadratic trace](../sdirk-eight-all-dirty-seven-quadratic-two-triple-d/README.md#normalized-quadratic-trace-and-literal-fourth-reads) also retains Hermite/repeated graph roots. For \(W\) with two simple roots, use
\[
 \sum_{\text{singleton }i}\frac1{g_i}
   =-\frac1r\sum_{W(\epsilon)=0}\frac{L_4'(\epsilon)}
                             {W'(\epsilon)L_4(\epsilon)}
      +\sum_{W(\epsilon)=0}\frac{A_2(\epsilon)}{L_4(\epsilon)}.
\]
Both sums are exact traces in the two-dimensional quotient by \(W\); a remainder \(a_0+a_1 t\) has trace \(2a_0-W_1a_1\), where \(W_1\) is the linear coefficient of \(W\). If \(W=(t-\epsilon)^2\), compute the unweighted singleton inverse via the negative derivative of \(H'/H\) at \(\epsilon\), which is
\[
 \frac1r\left[(L_4'/L_4)^2-L_4''/L_4\right](\epsilon)
                         +2A_2(\epsilon)/L_4(\epsilon).
\]
Here \(H'=L_4'\) and \(H''=L_4''-2rA_2\) at \(\epsilon\); no inversion of \(W'\) is made on this branch. Add \(\sum_{d\text{ D}}A_2(d)/L_4(d)\) for the doubled contributions. The weighted inverse sum is again the coefficient of \(t^7\) in the remainder modulo \(L_4^2\) of
\[
 \frac{H_3}{Q/B}\left(\frac{L_4}{rW}+A_2\right),\qquad
 H_3=4m^6/175,
\]
as given by the [signed Cauchy residues](../sdirk-eight-all-dirty-seven-affine-two-singletons/AFFINE-TRACE.md), whose algebraic derivation does not require \(W\) simple. The needed inverse denominators are coprime to \(L_4\) by consecutive Legendre coprimality.

Consequently this trace is \(c/r+\mathcal T(A_2)=0\), with \(c\) scalar and \(\mathcal T\) linear. Multiply by \(\lambda\) after substituting \(r=\nu\lambda\) and \(A_2\) above:
\[
                  \mathcal T(A_0)\lambda+c/\nu-\beta\mathcal T(T)=0 .
\]
This is the second affine row. The check tests both rows and keeps zero coefficients, zero-scale candidates, and duplicate physical pair guards distinct; no affine pivot is assumed invertible. In the nine remaining projections the two rows are inconsistent. All happen to have squarefree \(W\), but the check tests this explicitly before using its derivative.

## Replay

Run `python five_d_products.py` and `python check_five_d.py` (SymPy 1.14 and python-flint 0.8 tested). It takes under a second in the tested environment. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticFiveDPrefix.lean) checks the scale-free shape identities on Lean/Mathlib 4.36.0; the exact chronological and trace proof is not an end-to-end native Lean theorem. No finite-characteristic claim is made.
