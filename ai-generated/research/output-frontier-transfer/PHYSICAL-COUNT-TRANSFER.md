# When does a paid frontier actually save physical stages?

Fix a target order \(p\), a low tree cap \(q\), and \(a\coloneqq p-q-1\) adjustable Newton pivots. Let \(\ell\) be the number of mandatory final clocks from the actual old frontier criterion. The old tableau is unchanged. We may merge early output copies into old pure stages through size \(q+1\); all such donor clocks counted below are distinct and disjoint from the fixed pivots. Let \(h\) be the number of protected new (nonmerged) head rows we want to retain for future preparation. A tail with \(k\) distinct contributing sites and \(t\) early merges adds \(k-t\) stages and must have \(k\ge a+h+t\) in this prescribed pivot architecture. This is a construction budget, not a claim that every other extension needs that many adjustable rows.

## Exact exterior-site count over the real algebraic numbers

Suppose all \(\ell\) required clocks and all \(t\) donor clocks are real-algebraic and exterior to \((0,1)\), allowing the endpoints. In particular the forced Newton ladder is exterior when the prescribed strict common diagonal is negative. With a fixed selected set of \(t\) donors, the minimum certified physical increment in this architecture is
\[
 \Delta_{\mathrm{alg}}(\ell,t,h)
    =\max\!\left(a+h,\ \left\lceil\frac{p+\ell-t}{2}\right\rceil\right),
\]
provided the resulting total number of sites is at most \(p\).

Indeed let \(H\) be the hull of the \(\ell+t\) fixed exterior sites, and \(R\) the hull of the other \(k-\ell-t\) contributing sites. The polynomial \(HR^2\) vanishes at every site and has integral of one nonzero sign. Its degree must therefore be at least \(p\). This proves \(k\ge\lceil(p+\ell+t)/2\rceil\), even if the output weights are signed. Independently \(k\ge a+h+t\) by head and pivot capacity.

For achievability choose \(k\) to be the larger of those two lower values and take the roots of the monic orthogonal polynomial \(Q_n\) for \(H\,dX\), with \(n=k-\ell-t\), as the remaining sites. When \(n>0\) these are distinct and interior. Interpolatory quadrature has precision at least \(p-1\), and all its weights are nonzero. At a free root this follows by integrating its isolating square times \(H\). At a fixed root \(\zeta\), multiply the cofactor integral by \(Q_n(\zeta)\) and use orthogonality to obtain the nonzero integral of \(H/(X-\zeta)\) times \(Q_n^2\).

The rule may also be chosen to fail the next degree. Put \(d\coloneqq p-k\). If \(d=n\), the first missing degree is witnessed by \(H Q_n^2\). If \(0\le d<n\), replace \(Q_n\) by \(Q_n+\theta Q_d\) for a sufficiently small nonzero real-algebraic \(\theta\). It remains orthogonal to every degree less than \(d\); the exact degree-\(p\) test \(H(Q_n+\theta Q_d)Q_d\) has nonzero integral and zero quadrature. Simplicity, separation and nonzero weights persist from \(\theta=0\). When \(n=0\), necessarily \(k=p\), and the exterior hull itself witnesses the failure. Therefore the count can be attained by an ordinary exact-order Newton extension, not only a scalar width bound.

With unchanged \(t,h\), releasing \(r\) pins saves at most \(\lceil r/2\rceil\) of these algebraic scalar receiver rows, and saves none after the \(a+h\) pivot floor is reached. An extra eligible old donor has the same effect on the second term as a released pin. This is different from the number of earlier physical rows that can be reused for higher preparation.

## A sharp inexpensive rational chart and its limit

Consider rational exterior pins and \(R_0\) eligible exterior donor clocks. Restrict the scalar support width to \(p-1\) or \(p\), and keep \(0\le h\le q\). One has the exact minimum within these two widths
\[
 \Delta_{\mathbb Q}^{[p-1,p]}(\ell,R_0,h)=
 \min\!\left\{
 p-\min(R_0,p-a-h),\
 p-1-\min(R_0,p-1-a-h,p-2-\ell)
 \right\}.
\]
For width \(p\), choose all sites exterior. Interpolation is exact through degree \(p-1\); every cofactor integral and the next hull integral have nonzero sign. For width \(p-1\), at least one site must be unprescribed, since an entirely fixed exterior hull has nonzero integral. Given that space, choose all but one site exterior and solve the final node as \(z=I(XH)/I(H)\). It is strictly interior. The cofactor two-by-two moment determinants are nonzero by definiteness, and so are the full next-defect determinant and all output weights. This proves sufficiency and the displayed necessity of capacity in those widths.

Two implications matter when spending old stages to gain frontier access. If at least one new head row is reserved (\(h\ge1\)), this minimum is independent of \(\ell\); releasing exterior pins saves no physical stages in this rational chart, although it makes quadrature patterns more flexible. If \(h=0\) and the eligible donor list is held fixed, releasing one or more pins from \(\ell=a\) saves exactly one stage if \(R_0=q\), and otherwise saves none. Indeed for \(R_0\le q-1\) the width-\((p-1)\) route already merges every donor, while for \(R_0\ge q+1\) the width-\(p\) route already reaches \(a\) new stages. These conclusions do not exclude better rational rules with \(p-2\) or fewer sites, nor any non-Newton architecture.

There is also a practical sufficient count with interior fixed times. If \(e\) prescribed pin or donor nodes are interior, the generic one-solved-site argument works whenever there are at least \(e+1\) independent site parameters after counting the fixed sites and before solving \(z\). With only the \(\ell\) pins and \(t\) donors prescribed, this is \(p-2-\ell-t\ge e+1\). Thus each released pin frees one unit of slack in this parameter inequality, and one more if that pin was itself interior, until the pivot and head budget intervenes. This is a sufficient certificate, not a necessity for a particular signed hull.

## A genuine rational stage saving in the symmetric sample geometry

Here is a case where the same old tableau does gain a physical stage from the partial frontier, even when all auxiliary scalar choices must be rational. Take an odd integer \(j\ge3\), put \(q=2j-1\) and \(p=2q+1=4j-1\), and fix a negative rational common diagonal. Suppose an actual old order-\((p-2)\) seed already supplies the symmetric sample group in OUTPUT-SAMPLE-FRONTIER.md through size \(m=q+j\), and use those \(q\) rows as its stipulated eligible donor list. Require their clocks to be disjoint from the full ladder. Since \(q-j=j-1\) is even, the sample group pays the frontier through \(m\); only \(\ell=q-j\) pins are needed.

With that payment, a \(p-1\)-site rule can merge all \(q\) donors and adds exactly \(q=a\) rows. There are \(j-1\ge2\) independent nonfixed sites apart from the solved node, and the only interior fixed site is the midpoint, so the generic rational gates apply. No further pure head row is requested in this terminal comparison.

If one insists instead on keeping all the unrelieved \(\ell=a=q\) ladder pins, width \(p-1=2q\) with all \(q\) donors would use only the fixed clocks. Their hull has nonzero integral. Indeed the exterior reflected-pair hull is reflection-even and has constant nonzero sign on \((0,1)\), the midpoint factor is odd, and the product of the ladder factors, up to its constant sign, is strictly decreasing there because every pin is to the right of \(1\). Pairing reflected points shows the integral has strict nonzero sign. Thus the \((p-1)\)-site scalar rule cannot be exact; either one merge is lost or width \(p\) is used, in each case adding at least \(q+1\) rows in this comparison. This is a genuine one-stage rational gain for the specified seed data and pivot architecture, with a multi-pin release. It makes no unrestricted stage-minimum assertion and requires no new order-specific coefficient computation.
