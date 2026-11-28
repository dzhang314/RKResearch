# DIRK12/15: no-late nonzero ghost clocks force an exact two-row geometry

Continue the same nine-site early-return or ten-site earliest-extra-zero high-site equality chart as the [ordinary chronology proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md). Here assume **all four ghosts occur before the first nonzero ordinary live clock** \(a\), and all four ghost clocks are nonzero and distinct. Let \(b\) be the second ordinary live nonzero clock. Both live clocks are physically unique in these respective early reverse charts. The real interval is still **15–16**.

- If \(L_6'(a)\ne0\), the second live diagonal is zero and the first one is nonzero. Put \(x=b/a\), \(\delta=A_{aa}/a\). Then
\[
 (2x-1)L_6'(ax)=x^3(2x^2-6x+5)L_6'(a),\qquad
 20(x-1)^2\delta^2+(-12x^2+24x-9)\delta+2x^2-3x+1=0 .
\]
The real discriminant condition excludes whole clock-ratio intervals. For fixed \(a\), the first equation leaves at most five admissible \(x\); for each, the quadratic and actual read leave at most two first diagonals and determine the unique normalized masked cubic.
- If \(L_6'(a)=0\), the first ordinary live diagonal is zero and \(a\) is one of five fixed shifted Legendre derivative roots. The second live diagonal is the exact scalar ratio \(W(b)/W'(b)\) with \(W=X^2(X-a)^2(X-a/2)\). In particular its denominator cannot vanish.

The no-late chart with a numerical-zero ghost is outside this specific projection. The argument uses genuine grades five and six and ordinary causality, not an assumption of reverse precision at a live singleton.

## Two scalar profiles with affine ghost masks

For each affine \(Q\) on the ordinary clock, interpolate the unique scalar \(S\in XP_3\) with \(S(c_g)=h_g Q(c_g)\) on all four ghosts. The ghost clocks are distinct and nonzero, and \(h_g\ne0\), so this is a two-dimensional space \(\mathscr S\) of scalar profiles. Each true grade-four state \(\mathbf V_S=S(\mathbf c)-\mathbf hQ(\mathbf c)\) is zero through all ghosts and the origin. Its actual primitive on live rows is exactly \(JS\), because the true grade-five pure space is ghost-only. Also \(R\mathbf V_S\in F_6\) with \(R=CA-AC-A^2\), where the genuine live \(F_6\) line has profile \(X L_6'\). There are no ghost rows between \(a\) and \(b\) in this case.

First suppose \(L_6'(a)\ne0\). For any \(S\in\mathscr S\) with \(S(a)=0\), the genuine primitive is zero at \(a\). The actual \(R\mathbf V_S\) is also zero there by causality, hence zero on live rows by the true \(F_6\) profile. At \(b\) this gives \(-A_{bb}^2 S(b)=0\), since the physical input is zero before \(b\). Thus its primitive also vanishes at \(b\), whether the diagonal is zero or \(S(b)=0\). For any such nonzero \(S\), \(JS\) is a nonzero multiple of
\[
                            W=X^2(X-a)^2(X-b)
\]
by the double roots \(0,a\), the root \(b\), and the degree bound five. There is at least one nonzero \(S\) in this kernel by dimension; \(S(b)=W'(b)\ne0\) up to its nonzero scale. Consequently \(A_{bb}=0\), and the kernel of \(S\mapsto S(a)\) in \(\mathscr S\) is exactly the line of \(W'\).

Take \(S=W'\) and its corresponding genuine affine mask. Both actual inputs \(C\mathbf V_S\) and \(\mathbf V_S\) are zero through \(a\), and at \(b\) their primitive has no physical diagonal. In particular the actual \(AC\mathbf V_S\) is zero at \(a,b\). Its grade-six scalar error is \(-J(XS)\) there. Since \(JS=W\) and \(W(a)=W(b)=0\), integration by parts gives \(J(XS)(u)=-JW(u)\) at \(u=a,b\). With \(x=b/a\), the exact normalized polynomial integrals are
\[
       JW(a)/a^6=-(2x-1)/60,\qquad
       JW(b)/a^6=-x^4(2x^2-6x+5)/60 .
\]
The second is nonzero (the quadratic factor is positive over the reals). If \(2x-1=0\), the genuine grade-six error would be zero at \(a\) and nonzero at \(b\), impossible. Thus \(2x-1\ne0\). Comparison on the actual \(X L_6'\) line gives the claimed Legendre ratio.

## The first diagonal and the unique masked cubic

The cubic-fit impossibility in the [companion proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md) says that the affine correction \(Q=1\) cannot produce a cubic. The leading coefficient map on \(\mathscr S\) is therefore nonzero, so the genuine scalar cubics in \(\mathscr S\) form exactly a line, with nonconstant affine correction. A nonzero member is nonzero at \(a\) (the kernel of evaluation at \(a\) is the quartic line \(W'\)). Normalize its scalar coefficients and ordinary clock by \(S(a)=1,\ X\mapsto X/a\), in the sense that the normalized cubic is its original profile \(S(aX)/S(a)\). Write the result as
\[
                       S(X)=s_1 X+s_2X^2+s_3X^3,\qquad S(1)=1 .
\]
The actual normalized first diagonal is \(\delta=JS(1)\), and the actual tap from \(a\) into \(b\) divided by \(a\) is \(p=JS(x)\), because the true grade-five primitive at \(b\) has zero diagonal and only the earlier live \(a\) as nonzero source of the mask.

Set \(R_L=b L_6'(b)/(a L_6'(a))=x^4(2x^2-6x+5)/(2x-1)\). The actual \(AC\mathbf V_S\) grades at \(a,b\) (normalized) have values \(\delta,p\), respectively, since the prior nonzero source has clock \(1\) in both and \(b\) is explicit. Their pure discrepancies on the genuine \(F_6\) line give
\[
                  p-J(XS)(x)=R_L[\delta-J(XS)(1)] .
\]
The true commutator \(R\mathbf V_S\) has actual value \(-\delta^2\) at \(a\), and \((x-1-\delta)p\) at \(b\) in the normalized units: there is no intermediate live or ghost row between \(a\) and \(b\). Therefore
\[
                         (x-1-\delta)p=-R_L\delta^2.
\]
Clearing only \(2x-1\) in the first relation gives the equivalent linear coefficient condition
\[
  (2x^2-2x+3)s_1+(x^2+2x)s_2+3x^2s_3=0,
\]
since the remaining factor is \(-x^2(x-1)^2/6\ne0\). Combining it with \(s_1+s_2+s_3=1\) yields
\[
                 2(5x-3)p+x^4[(6x-10)\delta-x+1]=0 .
\]
Multiply the commutator by \(2(5x-3)\) and use this relation, without dividing by \(5x-3\). The exact remaining polynomial is
\[
       20(x-1)^2\delta^2+(-12x^2+24x-9)\delta+2x^2-3x+1=0.
\]
Since \(x\ne 1,1/2\), its constant \((x-1)(2x-1)\) is nonzero: \(\delta\ne0\). At \(x=3/5\) the preceding undivided relation specifically fixes \(\delta=1/16\), so the second root of the quadratic at that ratio is spurious. At any surviving ratio \(p=-R_L\delta^2/(x-1-\delta)\) is determined, with nonzero denominator by the commutator and \(R_L,\delta\ne0\). The three linear evaluations \(S(1),JS(1),JS(x)\) on the three cubic coefficients have determinant \(-x^2(x-1)^2/24\ne0\), determining the normalized cubic.

The real discriminant is
\[
                      -(2x-1)(8x^3+12x^2-30x+1)\ge0 .
\]
If \(r_1<r_2<r_3\) are the three real roots of this cubic, the exact Sturm isolation below establishes \(r_2<1/2<r_3\). Thus the only permitted ratio intervals from this test are \([r_1,r_2]\) and \((1/2,r_3]\), with \(0,1\) removed by the literal clock guards. The exact real-root replay isolates \(r_1\) in \((-2838/1000,-2837/1000)\), \(r_2\) in \((33/1000,34/1000)\), and \(r_3\) in \((1303/1000,1304/1000)\). No sign assumption on physical weights is needed.

## A first ordinary live Legendre root

If \(L_6'(a)=0\), the actual \(R\mathbf V_S\) is zero at \(a\) for every member, because its genuine pure space has profile \(X L_6'\). If all \(S(a)\) were zero, then actual \(A\mathbf V_S,AC\mathbf V_S\) would be zero at \(a\), and the respective true grade-five and grade-six errors vanish there, so \(JS(a)=J(XS)(a)=0\) for every member. Their degree-five primitives would span \(B P_1\), where \(B=X^2(X-a)^2\), by the two double roots and dimension two. The second integral would require \(I_a(W)=0\) for all of this span, using \(J(XS)(a)=a JS(a)-I_a(JS)\), but \(I_a(B)=a^5/30\ne0\). Thus some member has \(S(a)\ne0\) and the actual commutator forces \(A_{aa}=0\). Both primitive moments vanish for all members by actual chronology, including the genuine grade-six error zero at this first Legendre root.

For a nonzero \(S\in\mathscr S\) with \(S(a)=0\), the primitive hence lies in \(X^2(X-a)^2P_1\) with zero integral up to \(a\). The unique such line is generated by \(W=X^2(X-a)^2(X-a/2)\), since the \(X^2(X-a)^2\)-weighted average of \(X\) on the oriented segment is \(a/2\). At \(b\), the actual grade-five primitive is just \(A_{bb}S(b)\), because the mask is still zero before \(b\) and there is no late ghost. Thus \(W(b)=A_{bb}W'(b)\). If \(W'(b)=0\), then \(W(b)=0\) and \(b=a/2\) since \(b\ne0,a\); but \(W'(a/2)=B(a/2)\ne0\). Therefore its denominator is nonzero and the precise second diagonal ratio follows.

This is an exact analytic subchart calculus, not a full real nonexistence claim. The companion exact replay checks the moment elimination, roots, and guards, and its small native scalar companion formally checks the normalized quadratic and discriminant consequence.

    python3 -B verify.py
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenNoLateAffineMasks
    lake env lean AuditDIRKOrderTwelveFifteenNoLateAffineMasks.lean

The typed native scalar replay passed Lean/Mathlib 4.36.0, with only the usual standard axioms. It does not formalize the whole stage-space argument.

The companion [no-late numerical-zero ghost analysis](../dirk12-fifteen-rank3-invisible-no-late-zero-ghost/README.md) now supplies the same two-dimensional mask in that previously unaddressed case and exact equations for its allowed third or fourth physical positions.
