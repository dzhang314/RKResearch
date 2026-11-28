# DIRK12/15: chronological amplitude splits on three repeated scalar sites

Work in the [four-invisible-ghost fixed seven-site chart](../dirk12-fifteen-rank3-invisible-four-ghost-fixed-grid/README.md). Assume the eleven live rows repeat exactly three numerical labels, so their multiplicities are \(3,2,2\), and suppose the actual weighted reverse cubic \(\mathbf G\) is supported at **all three** of those labels. Then in true reverse physical chronology:

1. All three repeated labels have appeared before the first nonzero singleton live label.
2. At least one of the three labels has displayed differing normalized values \(G_i/b_i\) among its preceding live rows by that first singleton.
3. At least two of the repeated labels have displayed those differences before the second nonzero singleton.

These are exact chronological necessities, not an exclusion of the whole three-repeated-label chart. The real interval remains **15–16**.

Use \(N=A^{\mathsf T}\) in true reverse physical order with \(\mathbf y=\mathbf1-\mathbf c\), \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\) and reflected primitive \(JP(X)=\int_0^X P\). A singleton label here is a numerical label of exactly one live row, even if there is a zero-weight ghost at the same numerical clock. By the preceding chart, the reverse literal origin \(0\) is such a singleton and is the actual first physical row. The genuine \(\mathcal B_3,\mathcal B_4,\mathcal B_5\) vanish on all ghost and singleton live rows, and sum to zero separately at each live label. An amplitude split means two previously encountered live rows of the same repeated label with different \(G_i/b_i\); no ghost norm inverse is taken.

Let \(a,b\) be the first and second nonzero singleton live labels in this chronology, and let \(z_1,z_2,z_3\) be the repeated live labels. Both \(a,b\) are interior fixed Lobatto labels. In fact if the reflected label \(1\) is singleton, its row is the literal forward origin and hence the very last physical row. There are three nonzero singleton labels here, so this label cannot be the first two. If the reflected label \(1\) is repeated, it is not counted as a singleton in the first place.

## What must happen before the first singleton

At the actual live row \(a\), genuine scalar reverse primitive reads through degree four are exact, because \(\mathcal B_5\) vanishes there. If at most one repeated label \(z\) has appeared, the exact degree-four test \(X(X-a)(X-z)^2\) would vanish on all contributing physical weighted inputs but have nonzero definite integral to \(a\). If exactly two repeated labels \(z_1,z_2\) have appeared, the degree-four nodal test \(X(X-a)(X-z_1)(X-z_2)\) would imply \(3a^2-5(z_1+z_2)a+10z_1z_2=0\), already excluded on the fixed grid by the [one-active arithmetic](../dirk12-fifteen-rank3-one-active-third-debut/README.md). Thus all three repeated live labels have appeared.

If none of them has split before \(a\), choose the scalar cubic \(S\) interpolating \(S(0)=0\) and \(S(z_j)=G_i/b_i\) for the common amplitude among preceding live rows at \(z_j\). This polynomial is nonzero: at each of the two multiplicity-two labels the sum-zero, nonzero \(\mathbf G\) pair has both covectors nonzero. The actual grade-three weighted state \(\mathbf W(S)-\mathbf G\) is zero on every row before \(a\), including all ghosts. Its actual grade-five commutator under \(YN-NY-N^2\) is pure and therefore zero at this singleton row. The true diagonal factor at the first possible nonzero coordinate is \(-N_{ii}^2\) times the numerical input there. Thus either the input vanishes at \(a\) or its physical diagonal is zero. In either case genuine grade-four and grade-five primitive reads on the contrast and its clock lift force
\[
                               JS(a)=J(XS)(a)=0 .
\]
Together with \(S(0)=0\), these two moments uniquely fix the nonzero cubic up to scale as \(S(X)\propto X(10X^2-12aX+3a^2)\), by the fixed two affine moments (or the definite \(X\)-weighted Gram after scaling). Its value at \(a\) is nonzero, so the actual diagonal is indeed zero. Then the receiver at \(a\) can only use \(0,z_1,z_2,z_3\), and its exact scalar degree-four test on \(X\prod_j(X-z_j)\) would require its primitive to vanish at \(a\). The fixed unanchored coefficient below excludes this. Hence there is at least one genuine earlier amplitude split.

## The clean part of true grade six pays the second singleton

The actual forward grade-five state space contains all live-supported scalar profiles \(S\in P_5\) satisfying one linear compatibility constraint: interpolate the four ghost values \(S(z)/h_z\) by a quadratic. Factorial and polynomial orders in this statement are actual forward grades, not a claim about rooted order of a reverse tableau. The leading cubic coefficient is a nonzero functional on \(P_5\) because its four nonzero barycentric coefficients on the four distinct ghost clocks already act nontrivially on \(P_3\). Thus the allowed polynomials form a five-dimensional space. Their evaluations on the seven live labels are independent, since a degree-five polynomial vanishing at all seven is zero.

A true grade-six reverse pure covector annihilates the actual forward \(T_5\) by the paid \(6+5=11\) product. Its aggregate on the seven live labels is therefore in the annihilator of that five-dimensional profile space, a two-dimensional plane. Its value at the literal terminal (reverse physical first row) is zero, and the terminal live label is singleton. Requiring that aggregate terminal coordinate to vanish cuts the annihilator plane by one: otherwise the terminal coordinate vector would itself lie in the five-dimensional evaluation space, impossible for degree five because the other six nodes are distinct. Consequently the true \(\mathcal B_6\) numerical restriction to the reverse singleton live rows has rank at most one.

This restriction is nonzero at \(a\). Indeed the scalar grade-five input \(P=X(X-a)\prod_j(X-z_j)\) has true weighted numerical input \(\mathbf W(P)\) zero through the row of \(a\). Its actual primitive is zero, but its scalar primitive there is nonzero by the fixed interior anchored check below. Thus the pure grade-six discrepancy is nonzero at \(a\). A true grade-six pure vector zero at that physical row therefore vanishes on all singleton live rows.

## A second split is necessary before the next singleton

Suppose there is just one split label \(z\) before \(b\); there is already at least one from the first singleton. At each other repeated label the observed normalized cubic amplitude through the prefix before \(b\) is uniform. Set the affine correction \(Q=X-z\) and choose the scalar degree-at-most-four interpolant determined by
\[
 S(0)=S(a)=S(z)=0,\qquad S(z_j)=(G_i/b_i)Q(z_j)\quad (z_j\ne z),
\]
using any earlier live row at the unsplit \(z_j\). These are five distinct prescribed points. At least one unsplit group is one of the two multiplicity-two groups, whose first normalized amplitude is nonzero, so \(S\ne0\). The actual grade-four input \(\mathbf W(S)-\mathbf G Q(Y)\) is zero on every physical row before \(b\), including after earlier singleton \(a\) and including all split and unweighted rows.

The genuine grade-six commutator of that input is zero at \(a\), hence also at \(b\) by the preceding paid singleton projection. Had \(S(b)=0\), the true grade-five primitive would force \(JS\) double roots at \(0,a,b\), impossible at degree at most five. So \(S(b)\ne0\), and the actual commutator diagonal forces \(N_{i_bi_b}=0\). The genuine primitive is then also zero at \(b\), and the pure grade-five errors vanish on the singleton rows. Thus its scalar primitive is a nonzero multiple of \(X^2(X-a)^2(X-b)\): the double roots are \(0,a\) and the additional root is \(b\). But \(S(z)=0\) forces its derivative at the separate repeated label \(z\) to vanish, giving
\[
                              5z^2-(3a+4b)z+2ab=0 .
\]
The fixed derivative check excludes this on all ordered distinct nonzero triples. Thus at least two different repeated labels must split before \(b\).

## Exact coefficient checks

Write \(s_1=\sum_j z_j,\ s_2=\sum_{i<j}z_i z_j,\ s_3=z_1z_2z_3\). The unanchored primitive is
\[
 I_0=\int_0^a X\prod_j(X-z_j)\,dX
       =\frac{a^2}{60}(12a^3-15s_1a^2+20s_2a-30s_3).
\]
The anchored degree-five primitive is
\[
 I_1=\int_0^a X(X-a)\prod_j(X-z_j)\,dX
       =-\frac{a^3}{60}(2a^3-3s_1a^2+5s_2a-10s_3).
\]
In the second test the receiver \(a\) is genuinely interior by the singleton boundary argument; no endpoint case is assumed nonzero. The independent exact Python checker obtains nonzero residues for 360 unanchored, 300 interior anchored, and 120 derivative choices modulo \(1013\). The same split-prime transfer as in the [other fixed-grid packets](../dirk12-fifteen-rank3-one-active-third-debut/README.md) uses only the fixed real Lobatto root field. No arbitrary tableau coefficient or unknown ghost clock is reduced.

    python3 -B check.py

The fixed-prime checks in this note have an exact Python replay. The previously linked one-active pair and triple checks also have Lean certificates; no Lean certificate is claimed here for the new chronology tests or for the entire stage restriction.
