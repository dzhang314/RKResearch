# Low-law boundaries in the disjoint two-later-singleton chart

Keep the [disjoint (1,1) seven-clock hypotheses](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md): strict ten-stage SDIRK of ordinary order at least eight, all ten physical quadratic defects nonzero, exactly seven clocks over a characteristic-zero field, both endpoints singleton, and each physical first-three prefix with one later D and one later S but no shared D. Use **low/low** later-singleton laws (A3 or star at both ends). Then:

1. The \(R\)-scale line itself cannot vanish identically in the unknown scale.
2. \(H=2\) is impossible, including its exceptional \(R\)-line-zero case.
3. Equal normalized later S offsets \(a=b\) are impossible in mixed A3/star, in either actual orientation.

This does not exclude all low/low off-diagonal points, nor all equal offsets for the same phase on both ends. High-law phases are outside this packet. All assertions are characteristic-zero field results, not reality or sign tests.

## Actual \(R\)-line-zero split

Write \(a=s,\ b=H-t\). In the [scale notation](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md#singleton-offsets-and-two-paid-scale-rows), low/low gives
\[
 N_0=(a-2)H(H-b)-2H+a+b,\qquad
 M_0=(b-2)H(H-a)-2H+a+b,
\]
and \(N_0-M_0=(a-b)H(H-2)\). If both vanish, then either \(H=2\) or \(a=b\). When \(H=2\), the equation is \(5(a+b)-2ab-12=0\), so
\[
 b=\frac{12-5a}{5-2a}
\]
with \(5-2a\ne0\) (otherwise the equation has nonzero constant \(1/2\)). At \(H=2\) retain the paid \(K\)-line, which cannot lose its scale coefficient because the [simultaneous rank-zero case](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-rank/README.md) is impossible. Its exact rational scale is then substituted in the two paid cubic-graph coefficient rows. In each of A3A3, A3S, SS their univariate joint gcd has degree one and is removed by genuine clock/tap/graph guards. There is no generic pivot inversion in the lost \(R\) line.

Off \(H=2\), the \(R\)-line-zero locus has \(a=b\), and \(N_0=(H-a)[H(a-2)-2]\). Hence \(H=2/(a-2)\). With equal S offsets and equal S tap law the two quadratics' known values reflect at \(\lambda=1\), making the actual scale \(\lambda=1\) by the true nonzero rank. The two exact graph rows on this one-parameter curve give a guard-trimmed unit gcd for A3S. For each of A3A3 and SS exactly one irreducible degree-six factor survives, as recorded in the checker. It permits a final literal fourth-row check below.

## The other half-width case \(H=2\) and the exact three-way fourth check

If \(H=2\) and the \(R\) equation retains rank, \(N_0=M_0\) and \(\lambda=1\). The genuine \(R\) then has equal endpoint values at \(0,2\), and its additional paid S value with the low law forces \(R(y)=k(y)/2\). This immediately excludes any star on either side: the known star D residual would be **on** that same graph, contrary to the true graph-off property of a doubled pair.

For A3A3 with \(H=2,\lambda=1\), both \(C=A_2+B R=K\) and \(R\) have equal endpoint values, hence are even in \(w=y-1\). The exact singleton quartic \(L_4-R C\) is even with four distinct S roots, so the two nonendpoint S labels reflect and \(a=b\). The true graph \(R=(2-w^2)/2\) determines \(F_*=(L_3/L_4)\bmod(w^2-2)=7w/26\). Therefore the D cubic, up to its nonzero scalar, is \(w(7w^2-36)\). The two observed D clocks \(y=2a,2-2a\) are antipodal and distinct, so \(7(2a-1)^2-36=0\). The quadratic is irreducible and covers both signs.

At all three residual fields just described (this quadratic and the A3A3/SS sextics of the rank-zero curve), \(a=b,\lambda=1\), the two paid D clocks are opposite in the centered coordinate \(w=y-H/2\); write them \(\pm d\). The third D must be at the center: the graph \(R\) is even, \(L_4\) coprime to it, and \(F_*=(L_3/L_4)\bmod R\) is odd. Thus \(Q_0/R\) is an odd cubic with the actual three distinct D labels as its roots. The now-fixed even \(R,C\) are read from their endpoint and additional S values. With paid original D defect \(g\ne0\), its true graph-off and Legendre reads give
\[
 B=\frac{L_4(d)-g C(d)}{g(g-R(d))}, \quad A_2=C-B R,\qquad
 g_{\rm mate}=-L_4(d)/(B g).
\]
These are exact true nonzero pivots; parity gives the same mate value at both observed D labels. All four S are consumed, but each observed D label still has an unconsumed mate. Thus the forward fourth must be at \(d,-d\) using \(g_{\rm mate}\), or at \(0\) using either root of \(U(0,g_4)=0\).

The checker computes the [true affine fourth read](../sdirk-eight-all-dirty-seven-clock/README.md#literal-fourth-reads-including-singular-pivots) from the three actual paid forward residuals. In a star the quadratic interpolant and the second-defect factor are independent of the two legitimate orders; both are retained. In each exact field it checks the two direct mate discrepancies at \(d,-d\) and the exact unit gcd of the center quadratic with the affine read. All three allowed fourth labels fail. No affine fourth coefficient is inverted.

## Equal-offset A3/star, with no half-width restriction

For mixed A3/star orient A3 forward. If \(a=b\), the scale is again \(\lambda=1\) by symmetric paid S data and full nonzero rank. The D cubic must be odd in the centered coordinate, by the same even-graph argument. The observed D labels are \(p=2a,\ q=H-(2-a)\). Since their labels are distinct, they are either antipodal (which forces \(a=2/3\), forbidden by the actual A3 nonzero third tap), or one of them is centered. If \(p\) is centered \(H=4a\); if \(q\) is centered \(H=4-2a\). These are separate one-parameter charts. The exact two graph coefficient rows give a joint numerator degree five in each. The [true unshared D common-\(B\) row](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md#remaining-paid-graph-and-d-gates-without-a-hidden-clock-variable) has unit exact gcd with each degree-five joint row. This branch uses no actual fourth computation.

Run `SYMPY_GROUND_TYPES=flint python check_low_boundaries.py` with SymPy 1.14 and python-flint 0.8. All surviving fields are exact rational fields, including both embeddings of every finite clock factor. The shared scalar Lean gate for \(N_0-M_0\) is in the [scale companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointScale.lean); the entire tableau and elimination proof are not native Lean. The general stage interval is unchanged.

The exact arithmetic was independently replayed. Any accompanying Lean scalar statement is a draft, not asserted kernel-checked in this release.
