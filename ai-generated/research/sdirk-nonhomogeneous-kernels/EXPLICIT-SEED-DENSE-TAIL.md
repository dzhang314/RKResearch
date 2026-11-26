# What a small explicit seed can supply in a dense derivative decoder

## Main conclusions

Let \(q\ge1\), and let a lower-triangular \(s\)-stage tableau have an initial \(m\)-row explicit block, \(m\ge1\), followed only by nonzero diagonal entries. The entries following the block may vary; in particular they may all equal a prescribed \(\gamma\ne0\). Put \(c=A\mathbf1\) and \(M=\operatorname{diag}(c)\). Assume a fixed linear dense derivative readout \(B:K^s\to K[X]_{<q}\) exact on every tree through grade \(q\), over a field \(K\) with \(1,\ldots,q-1\) nonzero. The rooted-tree conventions are
\[
 \Phi_\bullet=\mathbf1,\quad
 \Phi_{[u_1,\ldots,u_a]}=\bigodot_j A\Phi_{u_j},\qquad
 g_\bullet=1,\quad
 g_{[u_1,\ldots,u_a]}=\prod_j\mathcal I g_{u_j},\quad
 \mathcal I X^b=X^{b+1}/(b+1).
\]
Thus \(B\Phi_t=g_t\) for \(|t|\le q\), with the grade counting all vertices.

If the seed has strict depth at most two, of any size, then
\[
 s\ge 1+\lfloor q^2/4\rfloor.
\]
Here strict depth is the maximum number of nonzero strict edges in a directed seed path, so a block of sibling stars has depth one. More generally the depth hypothesis can be replaced by \(A_S^3\mathbf1=0\) for the seed matrix \(A_S\); cancellation is allowed. For all seed sizes \(m\le4\), with any support and clocks, the same no-savings result holds. In fact for \(m=3\) or \(m=4\) the bound improves to \(s\ge2+\lfloor q^2/4\rfloor\), and for \(m=2\) it improves by one when \(q\) is odd. These are necessary conditions, not sharpness assertions for competitors with a fixed seed. They include genuinely distinct, live blocks, since no weight, liveness, or distinctness assumption is used.

The benchmark \(1+\lfloor q^2/4\rfloor\) is attained by the separate one-origin dense construction with any prescribed nonzero real diagonal, over a finite real algebraic extension for algebraic \(\gamma\). The present conclusion rules out a stage saving in the stated seed classes, even with a completely different dense readout and arbitrary edges into the nonzero-diagonal tail. A fixed single endpoint target alone is not a dense readout and is not covered by the stage-count conclusions.

## Tail rank and the exact missing seed modes

Write \(E_n=\operatorname{span}\{\Phi_t:|t|\le n+1\}\) for \(0\le n\le q-1\), and \(Z_n=\ker(B|_{E_n})\). Let \(\sigma\) restrict to the first \(m\) coordinates, \(V=\ker\sigma\) be the tail space, and \(c_S=\sigma c\). The first seed clock is zero. Put
\[
 U_n=\operatorname{span}\{c_S,c_S^2,\ldots,c_S^n\},\qquad
 \eta_n=\dim U_n-\dim(U_n\cap\sigma Z_n),
\]
with componentwise powers and \(U_0=0\). These quantities use actual paid stage jets. The exact tail target rank is
\[
 \dim B(E_n\cap V)=n-\eta_n. \tag{1}
\]
Indeed \(B(E_n)=K[X]_{\le n}\) by the bush trees \(M^a\mathbf1=c^a\). The map from this target onto \(\sigma E_n/\sigma Z_n\) sends a polynomial to the prefix of any representative modulo \(\sigma Z_n\); its kernel is exactly \(B(E_n\cap V)\). The classes of the prefix power vectors including \(\mathbf1\) span the quotient, again by the bush trees. Every member of \(\sigma Z_n\) has first coordinate zero, because the first stage evaluates the exact polynomial profile at zero for every tree. The constant class is therefore independent of the positive power classes. The quotient has dimension \(1+\eta_n\), proving (1).

Use \(\Pi=MA-AM-A^2\). Attaching a leaf to the root for \(M\), or a unary root for \(A\), raises the grade by one and acts on the exact polynomial by \(X\) or \(\mathcal I\). The identity \(X\mathcal I-\mathcal I X=\mathcal I^2\) on monomials shows \(B\Pi(E_n)=0\) when \(n+2\le q-1\), with \(\Pi E_n\subset E_{n+2}\). The space \(V\) is \(\Pi\)-invariant because the matrix is lower triangular, and \(\Pi|_V\) is invertible since its physical tail diagonal is \(-A_{ii}^2\). There need not be any invertibility on the whole stage space.

Let \(n_j=q-1-2j\), using the nonnegative terms of this progression. For each \(j\), choose representatives in \(E_{n_j}\cap V\) of a basis of its tail target in (1), and apply \(\Pi^j\) to them. These vectors are independent in \(V\). If there were a relation, divide within \(V\) by the least power \(\Pi^{j_0}\) occurring in it, then apply \(B\). All resulting terms lie in \(E_{q-1-2j_0}\) by the paid degree count. Terms with positive remaining powers have zero target, and the terms of least power have independent targets. This contradicts the choice of \(j_0\). Since \(\sum_{j:n_j\ge0} n_j=\lfloor q^2/4\rfloor\), the dimension bound is
\[
 s\ \ge\ m+\lfloor q^2/4\rfloor-\sum_{j:n_j\ge1}\eta_{n_j}. \tag{2}
\]
This is the invertible dense tower applied to a physical tail and its exact restricted targets. It is independent of any bound obtained from the corank of the full singular commutator.

## A broadly applicable depth-width charge

Let \(r\) be the number of distinct nonzero seed clocks; always \(r\le m-1\). Let \(d\ge0\) satisfy \(A_S^{d+1}\mathbf1=0\), e.g. the strict depth. For every \(a>d\) with \(a\le n\) the tree with \(a\) unary extensions has actual jet \(A^a\mathbf1\) and exact profile \(X^a/a!\). Thus
\[
 c^a-a!A^a\mathbf1\ \in Z_n,\qquad
 \sigma(c^a-a!A^a\mathbf1)=c_S^a\quad(a>d).
\]
The latter equality holds because the prefix is lower triangular, hence closed under its own row actions. The rank of any \(h\) consecutive positive powers of \(c_S\) is \(\min(r,h)\): remove zero-clock rows and duplicate clock values, then scale each remaining row by its first nonzero power and use Vandermonde. In particular
\[
 \eta_n\le \min(r,n)-\min(r,(n-d)_+).
 \tag{3}
\]
The right side counts the integers in \([1,r]\cap[n-d+1,n]\). In (2) the values \(n\) differ by two. If \(d\le2\) their charge intervals are disjoint, so the total charge is at most \(r\) and \(s\ge m-r+\lfloor q^2/4\rfloor\ge1+\lfloor q^2/4\rfloor\). For any \(d\ge1\) the total is bounded by \(r\lceil d/2\rceil\), or more sharply by simply using (3) at the actual paid parity and cap. Thus deeper seeds with sufficiently many repeated or zero clocks are covered as well.

For a seed support of strict depth at most one, every strict donor has a zero row, and hence the same rooted profile as the origin. In the seed a bush of grade \(a+1\) has value \(c_S^a\) and every non-bush of that grade is zero. Since leaf and size-two grades each have only one tree, \(\sigma Z_n=\operatorname{span}\{c_S^2,\ldots,c_S^n\}\), empty for \(n\le1\). The reverse containment follows already from the tall defects above; the forward containment follows by decomposing any paid relation by grades, since distinct grades have independent monomial profiles. Consequently (3) is exact for the missing target rank in this sibling class. Its total charge is the number of integers \(1\le n\le\min(r,q-1)\) congruent to \(q-1\) mod 2. For example it is at most \(\lceil r/2\rceil\), and with distinct nonzero sibling clocks this yields at least \(\lfloor r/2\rfloor\) additional stages above the one-origin benchmark.

## Complete all-grade 2–4-row consequence

The following refinements of (3) use only paid target-null jet directions. Put \(N=[M_S,A_S]-A_S^2\), the seed restriction of \(\Pi\), where \(M_S=\operatorname{diag}(c_S)\). In any paid cap \(n\ge2\) the space \(\sigma Z_n\) contains
\[
 N\mathbf1,\ Nc_S,\ldots,Nc_S^{n-2}.
\]
It also contains \(u=N\mathbf1\), \(M_Su\), \(M_S^2u\) at their respective caps \(n\ge2,3,4\), and \(A_Su\) at \(n\ge3\). These follow by using \(\Pi\) on the appropriate bush, or by applying \(A\) or \(M\) to the preceding actual target-null jet; each addition costs exactly one grade and preserves zero polynomial target. All arguments below concern caps that are actually present in \(n=q-1,q-3,\ldots\); bounding the entire parity progression only enlarges its charge.

For a complete adjacent seed chain with distinct clocks and all \(m-1\) adjacent coefficients nonzero, \(N\) on rows \(2,\ldots,m\) and columns \(1,\ldots,m-1\) is triangular with nonzero diagonal \((c_i-c_{i-1})A_{i,i-1}\); the last column of \(N\) is zero. The displayed \(N\)-defects have rank \(\min(m-1,n-1)\) at \(n\ge2\) by Vandermonde on the first \(m-1\) clocks. They live in the \(m-1\) dimensional space of first-coordinate-zero seed data, so
\[
 \eta_n\le \min\{n,(m-n)_+\}\quad(n\ge1).
 \tag{4}
\]
For \(n=1\) this follows directly from the power span, so this statement does not use an unpaid defect. Notice that distinct adjacent clocks are enough for the nonzero diagonal, and distinct first \(m-1\) clocks for the rank; pairwise distinct clocks suffice for both.

For \(m=2\), either \(r=0\), or the seed has just one nonzero star clock and the only possible charge is at \(n=1\) by (3). The latter cap occurs only for even \(q\). This gives the announced bound, including the extra stage for odd \(q\).

For \(m=3\), if \(r\le1\) the charge is at most 1 by \(d\le2\). If \(r=2\) and \(d\le1\), the only possible charges are \(n=1,2\), at most one of them in a given parity. Otherwise the two consecutive seed edges are nonzero, all clocks are distinct, and (4) again gives total at most 1. Thus (2) gives at least one stage more than the one-origin benchmark.

For \(m=4\), choose \(d\) to be the largest \(a\) with \(A_S^a\mathbf1\ne0\), so \(d\le3\). If \(r\le1\), (3) charges at most 2. Also if \(r\le2\) and \(d\le2\), it charges at most 2. For \(r=3\), \(d=3\), the unique possible length-three seed path forces all adjacent seed coefficients nonzero, and (4) bounds the successive charges at \(n=1,2,3\) by \(1,2,1\), with all later zero. Thus either parity charges at most 2.

The remaining four-row charts have the following uniform paid reductions:

* If \(r=3\) and \(d\le2\), then \(u=N\mathbf1\) has \(u_2=c_2^2\ne0\). At \(n=3\), the high tall defect \(c_S^3\) is present, and \(u,M_Su\) cannot both lie in its line: if the nonzero \(u\) lay in it, then \(M_Su\) would be a nonzero multiple of \(c_S^4\), independent at the three distinct nonzero clocks. Hence \(\eta_3\le1\). At \(n=4\) the tall powers span the plane \(\operatorname{span}(c_S^3,c_S^4)\). If \(u,M_Su,M_S^2u\) were all in this plane, interpolation by the three nonzero clocks would put the isolated nonzero second coordinate of \(u\) in the plane. This is impossible: a vector in that plane vanishing at the two other nonzero clocks has a linear coefficient polynomial with two distinct roots and is zero. Thus \(\sigma Z_4\) spans all the first-coordinate-zero seed data and \(\eta_4=0\). The possible remaining charges obey \(\eta_1\le1,\eta_2\le2\) and are zero from \(n=5\) on by (3); either parity has total at most 2.

* If \(r=2\) and \(d=3\), the unique full seed path again has all adjacent coefficients nonzero. Now \(u_2=c_2^2\ne0\), whereas \((A_Su)_2=0\) and \((A_Su)_3=A_{32}c_2^2\ne0\). Thus \(u,A_Su\) span a plane in the three-dimensional first-coordinate-zero space. At cap 3 it meets the two-dimensional pooled positive-power space in a nonzero vector \(v\in\sigma Z_3\cap U_3\), giving \(\eta_3\le1\). At cap 4 the high tall defect \(c_S^4\) is present. If \(v\) is proportional to it, then \(M_Sv\) is proportional to \(c_S^5\) and independent of \(c_S^4\) at the two distinct nonzero labels. If \(v\) was not proportional, it itself is independent. Both \(v\) and \(M_Sv\) are available at cap 4; \(c_S^5\) here names only the restricted vector, produced by applying the single paid clock mark, not a new size-six tree. Hence the pooled positive power space lies in \(\sigma Z_4\) and \(\eta_4=0\). The same remaining charges as in the preceding case finish the proof.

Thus every four-row seed has total at most 2 in (2), giving the strict penalty asserted. All arguments work also when the tail is empty, in which case (1) forces the claimed target ranks in the zero-dimensional tail to vanish.

## Why extra permanent orthogonal anchors fail

The following is a distinct obstruction to a direct generalization of the anchored Laguerre decoder. It does not require the tail result. Work in characteristic zero, with \(T=\mathcal I-\gamma\). If the permanent base is to decode a polynomial quotient \(K[X]/(P)\) with monic \(P\) of degree \(a\ge1\), and its remainder ideal is \(T\)-invariant, then \(P=X^a\). In fact already \(\mathcal I P\in(P)\) suffices. Write \(\mathcal I P=(X-\lambda)P/(a+1)\) by leading degree, differentiate, and get \((X-\lambda)P'=aP\). Expanding at \(\lambda\) gives \(P=(X-\lambda)^a\); the primitive vanishes at zero, so \(\lambda=0\). Conversely the ideal \(X^a K[X]\) is \(T\)-invariant. This rules out replacing the origin by several fixed distinct orthogonal node anchors with the same invariant-ideal mechanism.

No fixed linear readout of an \(m\)-row seed with \(r\) distinct nonzero clocks can supply \(K[X]/(X^a)\) through \(q\ge a+r\) for \(a\ge2\). The \(r\) paid bush vectors with powers \(a,\ldots,a+r-1\) must all map to zero in the quotient. They span the pooled nonzero clock space by Vandermonde, in particular the clock vector. But the size-two tree must map to \(X\bmod X^a\ne0\), a contradiction. If \(r=0\) the clock contradiction is immediate. Thus an extra permanent linear Taylor anchor is not being supplied by a fixed small live ERK block. At the pointwise level there is an even earlier obstruction: the first nonzero explicit clock has \((Ac)_i=0\) because all its strict donors have earlier zero clocks, yet exact grade 3 requires \(c_i^2/2\ne0\).

There is also a direct obstruction to replacing a whole initial Laguerre chart while leaving its full paid-band proof unchanged. In the one-origin chart \(W_j=j!(\mathcal I-\gamma)^{j-1}X\), the coefficient of \(W_1\) in \(X^a\) is \(a!\gamma^{a-1}\) for \(a\ge1\). An algebraic check is to apply the linear functional \(X^a\mapsto a!\gamma^{a-1}\) to the explicit \(W_j\) coefficient formula; the result is 1 at \(j=1\) and the alternating binomial sum zero for \(j>1\). An \(m\)-row ERK seed has identically zero tall jet at grade \(m+1\), whereas its exact polynomial profile has \(W_1\) coefficient \(\gamma^{m-1}\ne0\). At a chart of level \(k\), the full anchored band forces this coefficient to agree whenever the grade is at most \(2k-1\). For \(q\ge m+1\), no linear seed readout can therefore replace such a chart unless \(m\ge2k-1\). In particular a block of two to four explicit rows cannot save stages by literal full-band early-chart replacement in this regime.

Neither permanent-anchor obstruction asserts that a changing, nonideal seed model, a more complicated hybrid with deeper larger seed, or an ordinary fixed-endpoint construction is impossible. The dense no-savings conclusions for the stated actual seed classes instead come from (1)–(4), independent of any orthogonal template or endpoint-only stability question.
