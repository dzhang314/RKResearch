# How the short echo compares with published upper bounds

Published basis: ai-generated/CURRENT.md and ai-generated/upper-bounds/README.md at the read-only archive commit 9596fae. The rational strict-SDIRK uppers in increasing orders \(1,\ldots,20\) are
\[
  1,1,3,4,5,7,11,13,19,21,28,29,37,39,48,50,60,63,74,77.
\]
Orders three to seven are supported by the separate small-order and checked rational documents. The corresponding real-algebraic uppers are
\[
 1,1,2,3,5,7,9,11,14,17,20,23,26,30,34,38,43,48,54,59.
\]

The two-row or three-row rule would be a favorable count if its partial-order profile were already available. The strongest real-algebraic source counts exclude that profile on any stage matrix of those counts for \(7\le d\le18\): the published lower bound at \(d+2\) is greater even than the source upper plus three. At \(d=5,6\), the source upper plus two already contradicts the target lower, and the cited rational witnesses have the required old clock \(1-\gamma\), as well as stronger direct negative evidence: their published literal tests fail every next-order equation. This is an obstruction to the stated partial-order interface on compact seeds, not an additional unrestricted bound.

The rational costs leave room at larger orders, but the already archived rational Newton witnesses at orders 8–20 have an explicit first-unpaid bush. The echo leaves those scalar outputs unchanged, so it cannot directly lift them or be credited with any new upper. A new compatible old output, or a redesigned partial-order seed with two orders of scalar slack, is essential. For a given stage matrix the exact prerequisite is linear in its old weights: match the desired rooted moments for every untouchable pattern. Full rank of the paid tree columns already rules out reweighting a known output. Neither predicate is inferred from the number of stages.

## A reusable rational source of the partial profile, not a better count

The profile is nonempty in a finite rational family that makes the two missing root classes intentional. Begin with an arbitrary exact rational strict SDIRK seed of order \(p-2\), with \(\gamma\ne0\), for target \(p\ge4\). Use the ordinary paid Newton-tail construction with cutoff \(q=\lfloor(p-1)/2\rfloor\) and \(a=p-q-1\), but impose only the leading coefficient match in every adjoint:
\[
 G P_j=\gamma P_j-P_{j+1}/(j+1),\qquad
 P_j(X)\coloneqq\prod_{i=1}^j(X-\eta_i),\qquad
 h_j\coloneqq J^*X^j-GX^j.
\]
Choose the first two reversed sites \(\eta_1,\eta_2\) freely and distinct, where the second is needed as an actual pivot even if the higher conditions are empty. For \(j\ge2\), choose \(\eta_{j+1}=\bar\eta-(2j-1)\gamma\), where \(\bar\eta=(\eta_1+\eta_2)/2\). Apply this whenever a clock in the paid list is needed. Then \(\deg h_0\le0,\deg h_1\le1\) and \(\deg h_j\le j-1\) for \(2\le j<a\). Indeed the second-leading coefficient only requires that successive reversed means differ by \(\gamma\); the low basis polynomials have degrees at most 1 and do not spoil the j-th cap for \(j\ge2\).

One exact rational quadrature has \(p-1\) sites: choose these \(a\) pivots and all other fixed sites distinct and negative, possible by translating the free pair far enough left and avoiding finitely many differences. The remaining site is \(z=I(XH)/I(H)\), where \(H\) is the degree-\((p-2)\) fixed-site hull. Then \(z\in(0,1)\), since \(H\) has constant sign there. The full hull \((X-z)H\) pays precision \(p-1\). The interior site's weight is nonzero by \(I(H)/H(z)\ne0\). For any exterior site \(u\), its cardinal numerator is \(I((X-z)H/(X-u))\), strictly nonzero: in the positive measure proportional to \(H\,dX\) this is the covariance of \(X\) and the strictly decreasing function \(1/(X-u)\). The covariance sign follows by integrating \((X-Y)(1/(X-u)-1/(Y-u))/2\) against two copies of the measure. The first unpaid bush witness is \(I((X-z)^2H)\ne0\). All coordinates are rational for the original rational \(\gamma\).

The preliminary low feed and Vandermonde correction remain those of the paid Newton proof, now requiring the old exact readout for \(h_j\) only where its cost fits. On every size-\(m\) child with \(m+j\le p-2\) it fits because \(\deg h_j\le j\). Hence the provisional tableau has order at least \(p-1\). At size \(p\) a root with its unique high child and \(j\ge2\) other root-leaf units is still paid: \(\deg h_j\le j-1\) gives \(m+\deg h_j\le p-2\). The decorated child terms of the polynomial adjoint then have largest root-child size at most \(m-1\le p-4\), so even when they attain size \(p\) they are among the same paid shapes. Induction on largest child gives the original proof on precisely this downward-stable collection. The cases with no high child are exact by scalar quadrature. The only unproved size-\(p\) output patterns are therefore a unary root or a root with one child of size \(p-2\) and a single leaf. The first possible one-large restriction uses \(2(q+1)+1>p\).

Take \(d=p-2\) in the echo theorem. The provisional stage system already has order \(d+1\), hence no special echo clock is needed. Two more rows finish exact order \(p\); the scalar witness survives. This yields a uniform rational exact construction using the old stage count plus \(p+1\) physical rows, before any optional protected old-row merges. It deliberately releases the first two adjoint coefficients at the cost of two high-order echoes. This proves feasibility of a common-diagonal architecture with these weakened pins, but by itself does not beat the existing \(p-1\)-site rational continuation, which often already uses old receiver merges. No tableau checker, compiler, solver, repository change, or held computation is part of this note.
