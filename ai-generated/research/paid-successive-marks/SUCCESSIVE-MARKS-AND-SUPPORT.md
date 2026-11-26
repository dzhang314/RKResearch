# Successive marks and simultaneous head ranks

This argument works for the genuine reviewed Runge–Kutta order conditions and actual physical row restrictions. It sends no array to a quotient that is presumed to satisfy those order conditions.

## Actual setup

Let \(A\) be lower triangular, \(c=A\mathbf 1\), and \(C=\operatorname{diag}(c)\). Let \(E_j,F_j\) be the native numerical and defect spaces at grade \(j\). Write \(J_0\) for formal integration from zero, and side conditions called paid below mean the positive integer divisors are units supplied by the achieved order \(p\).

Fix \(k,H\) and \(m\coloneqq H-k\), with \(H\le p\). Let \(S\) be any set of actual rows containing the support of every \(F_H\) vector. Suppose \(\mathbf a\in F_k\) agrees with \(XP\) evaluated at the clocks on \(S\), for some polynomial \(P\) of degree at most \(d\), with \(d+1\le k\). This is a single simultaneous restriction: \(\mathbf a\) may mix any number of heads, degree profiles, and core columns, and may have arbitrary actual overlaps. No per-head reduction or choice of representatives is needed.

## The universal mark count

For any integer \(r\) satisfying
\[
 1\le r\le m-1,\qquad 2(k+r-1)+1\le p,
 \qquad d<r(m+1-r),
\]
the simultaneous match implies \(P=0\).

To prove this, suppose \(P\ne0\) and set \(W\coloneqq XP\). At the a-th mark, with \(1\le a\le r\), define the filter and adjusted input by
\[
 B_{a-1}\coloneqq\prod_{j<a}(X-u_j),\qquad
 z_a\coloneqq (B_{a-1}W)(c)-B_{a-1}(c)\odot\mathbf a .
\]
Here the \(u_j\) are the previously marked clocks and \(B_0=1\). The displayed adjustment belongs to \(F_{k+a-1}\) by paid multiplication, while the polynomial has degree at most \(k+a-1\). The unanchored coefficient separation at this actual grade proves \(z_a\ne0\). This uses only \(2(k+a-1)+1\le p\), not a zero physical row. A version of the shifted Cauchy proof can save one condition here because the constant term of every \(B_{a-1}W\) is already zero.

Since \(z_a=B_{a-1}(c)\odot z_1\), its support lies off \(S\). At its first nonzero row \(i_a\), the local Volterra pivot at cost \(k+a+1\le H\) forces the actual diagonal of \(A\) there to vanish. Also the filtered adjustment is zero there, so \((B_{a-1}W)(c_{i_a})\ne0\). The new clock \(u_a\coloneqq c_{i_a}\) is therefore nonzero and different from all earlier clocks. The next filtered residual vanishes through row \(i_a\), so the rows are strictly chronological. By the paid local primitive lemma these rows give
\[
 J_0(R B_{a-1}W)(u_a)=0\qquad(\deg R\le m-a).
\]

For clarity, the algebraic readout now uses no matrix. Define
\[
 T_a\coloneqq J_0^{\,m-a+1}(B_{a-1}W).
\]
The centered moment identity gives \((X-u_a)^{m-a+1}\mid T_a\). The constant-term payment and the integral degree bound give
\[
 X^{m-a+2}\mid T_a,\qquad
 0\ne T_a,\qquad
 \deg T_a\le d+m+1.
\]
Nonzero follows by differentiating the paid iterated primitive; the polynomial input and all iterates have degree at most \(d+m+1\le H\).

The exact successive-primitive identity is
\[
 T_{a+1}=(X-u_a)T_a'-(m-a)T_a .
\]
It follows from the paid integration-by-parts identity for \(J_0^n((X-u)P)\). The current factor at \(u_a\) loses no multiplicity in this step: a derivative loses at most one, which the leading factor \(X-u_a\) restores. At any earlier site, each subsequent step loses at most one. Therefore at step \(r\) all the earlier \(r-1\) sites still have multiplicity \(m-r+2\), as does the origin; the last site has multiplicity \(m-r+1\). The clocks and origin are all distinct. Consequently
\[
 \deg T_r\ge r(m-r+2)+(m-r+1)=(r+1)(m-r+2)-1 .
\]
Comparison with \(d+m+1\) gives \(d\ge r(m+1-r)\), contradicting the stated threshold. There is no sign, root reality, or ordering of the distinct clock values.

For one mark this excludes degree at most \(m-1\); for two, degree at most \(2m-3\); for three, at most \(3m-7\). The physical restriction \(r\le m-1\) matters because the diagonal itself costs two grades. For two marks and \(m=3\) this still excludes cubics; for \(m=5\) it excludes degree seven, rather than only degree six in the earlier sufficient statement.

## A simultaneous rank consequence

Let \(\mathcal L\) be the actual stage subspace supported in \(S\), zero at its zero clocks, and constant on each part of a nonzero clock fibre lying in \(S\). Its dimension \(\nu\) is the number of distinct nonzero clocks represented in \(S\). This is the exact range of weighted evaluation with weight \(\mathbf 1_S\odot c\), by interpolation on the genuine nonzero clock labels. Let
\[
 \mathcal B_d\coloneqq
 \{\mathbf 1_S\odot (XP)(c):\ \deg P\le d\}
 \quad\text{and}\quad
 t\coloneqq\dim(F_k\cap\mathcal L).
\]
The theorem applied to the zero adjustment gives \(\dim\mathcal B_d=d+1\). Applied to an arbitrary simultaneous adjustment it gives \(\mathcal B_d\cap F_k=0\). Counting both spans inside their respective original-coordinate spaces gives
\[
       \nu\ge d+1+t,\qquad |S|\ge d+1+\dim F_k .
\]

The first bound has an exact contrast formulation. Take one representative row of \(S\) at each nonzero clock. Map \(F_k\) to its coordinate values at the zero clocks and to its differences from the representative on each other row of each nonzero fibre. This is an actual linear map \(\Delta\), with kernel \(F_k\cap\mathcal L\), because \(F_k\) already vanishes off \(S\). Thus the bound is
\[
          \nu+\operatorname{rank}\Delta\ge d+1+\dim F_k .
\]
This counts genuine whole-fibre head directions, and subtracts actual repeated-clock contrasts. It does not count head labels or treat the separate head restrictions as independent.

For examples: two marks give the additional clock or row counts \(4,5,6,8\) at \((k,H,p)\) respectively \((4,7,11),(5,9,13),(6,10,15),(8,13,19)\), provided the same support and rank conditions hold. These are reusable rank bounds, not claims of new absolute stage bounds at those orders. One still needs independent information on the number of rows excluded from \(S\), a cap on its nonzero clocks, or lower rank for its matching whole-fibre directions.

A finite obstruction to counting head labels is visible over \(\mathbb Q\). At each of \(\nu\) distinct nonzero clocks take exactly three physical rows, with two head restrictions \((1,-1,0)\) and \((0,1,-1)\). All polynomial powers of both heads continue to give vectors of coordinate sum zero on each fibre. Their span can have dimension \(2\nu\), but intersects the fibre-constant line trivially at every fibre. Individual chosen coordinates may look interpolable while the simultaneous restriction never gives a nonzero constant line. This is a numerical restriction example, not a proposed RK tableau.

## Vector-valued terminal observations

Suppose a true endpoint \(F_H\) is not known to vanish at the chosen marks, but its measured gauge kernel \(Z\coloneqq F_H\cap\ker L\) does, for a linear map \(L\) to any finite-dimensional observation space. Let \(W_0\subseteq F_H\) be the span of genuine candidate outputs already known to vanish at all the marks. If \(L(W_0)=L(F_H)\), the cut extends to all of \(F_H\): subtract a witness with the same measurement, leaving a vector of \(Z\). If the observed span is smaller, this argument alone cannot guarantee the cut, since some functional on the quotient can be zero on the observed span without being zero everywhere.

For the chronology above, the last filtered carrier \(z_r\) is zero strictly before row \(i_r\). Its grade is \(k+r-1\) and this last diagonal is zero. The genuine Volterra outputs
\[
 D(C^j z_r),\qquad D\coloneqq CA-AC-A^2,\qquad 0\le j\le m-r-1
\]
are zero at every selected mark and are paid into \(F_H\). If \(F_{H-1}\subseteq Z\), all but the highest power of this single trajectory automatically have zero gauge. One trajectory then gives at most one nonzero measured direction in the top quotient, regardless of how many distinct marks it produces. For a higher-rank remainder one needs other genuine inputs with the same actual prefix cutoff and independent measured images, or must directly verify the corresponding primitive outputs. Separate per-head chronology is not enough.

## Source boundary

The staged sources provide the basis-free rank accounting and a consumer using the existing two-mark statement, the paid primitive transition with the two root-propagation lemmas, and the vector-valued linear observation certificate. The general r-step theorem and the sharper degree windows above are the complete paper argument, not checked Lean claims. The exact two-mark source consumer currently retains the previous small scalar-degree hypotheses until the sharper scalar proof is admitted. No compiler, solver, replay, repository write or held-path access was performed.
