# A lower-word cut excludes generic minimum-width repaired odd banks

This gives a lower-word rank obstruction for the specified direct strict-SDIRK architecture with zero early output weights. It does not impose the last word length or give an unrestricted stage bound.

## 1. The actual cut test

Work over the reals with an algebraic real common diagonal \(\gamma<0\), two distinct negative genuine early anchors \(\alpha,a\), and
\[
 D(X)\coloneqq (X-\alpha)(X-a),\qquad
 J\coloneqq I_0-\gamma I,\qquad J^*\coloneqq I_1-\gamma I,\qquad
 \ell(F)\coloneqq\int_0^1 F(X)\,dX .
\]
Here \(I_0\) and \(I_1\) are polynomial integration from zero and to one. As in [actual double-factor inputs](ACTUAL-DOUBLE.md), the early bank is closed, all its weights are zero, and has actual earlier-null heads attaining \(D\mathbb P_{\le n-3}\) at every size \(n\ge m+1\), whose true late data are their pure clock evaluations. Let the distinct actual physical late clocks be \(x_1,\ldots,x_d\), let \(C\) be their diagonal, \(T\) any real strict lower late matrix, \(E\) their evaluation map, and \(b\) the actual late weight row. For a word \(w\) of length \(k\) (the number of marks or strict edges), let \(a_w\) be the row obtained from \(b\) by right multiplication by \(C\) or \(T\); let \(P_w\) be the polynomial from \(1\) by multiplication by \(X\) or application of \(J^*\), in the same order. Denote the row span through length \(k\) by \(V_k\). The claimed cut uses only the necessary actual contacts
\[
 a_w EF=\ell(P_w F),\qquad
 F\in D\mathbb P_{\le p-k-3},\quad k\le r-1,\quad p=m+r,\ r\le m .
 \tag{1}
\]
These follow from grafting the actual earlier-null heads and do not invoke any mark tests at length \(r\). Indeed a strict primitive preserves earlier-null data and acts on the late numerical column by \(T\), while a mark acts by the literal clock diagonal. Scalar and other order conditions may impose more.

The assignment \(a_w\mapsto P_w\) is well defined on \(V_k\) whenever \(p-k-3\ge k\): a numerical relation gives a polynomial \(P\) of degree at most \(k\) orthogonal to \(D\mathbb P_{\le p-k-3}\); testing it against \(DP\) uses positivity on \([0,1]\). This proves model consistency through \(r-1\) in the odd balanced case \(m=r+1\), and through \(r-2\) in the even balanced case \(m=r\). The cut itself needs consistency only through \(r-2\).

For an even target, consistency through \(r-1\) additionally follows after testing its words on two actual earlier-null complementary heads, without using any word of length \(r\). To produce these heads, strictly extend old-null models \(F\in K_m\) by one unary: their repaired early data are zero because the only possible child value there is in the last coordinate. Their exact profiles \(JF\) have two independent anchor evaluations \(E_\alpha J,E_a J\), as in the sampler choice. Together with the true double ideal they span the exact polynomial space \(\mathbb P_{\le m}\) by dimension. The actual late data of these two heads need not equal pure evaluations. A numerical row relation annihilates their actual data regardless; genuine rooted order prescribes the corresponding two formal moments. The full Hilbert pairing with \(\mathbb P_{\le m}\) now proves model consistency through \(r-1\).

Wherever the assignment is well defined its model is onto \(\mathbb P_{\le k}\) by pure marks. With \(B\coloneqq T+\gamma I\), the literal operator \(\Omega\coloneqq BC-CB+B^2\) has zero model in the \(X\)-coordinate for right rows: \(X I_1-I_1 X+I_1^2=0\). Its diagonal is \(\gamma^2\), hence it is invertible. It maps \(V_{k-2}\) injectively into the model-zero subspace \(N_k\), giving
\[
  \dim V_k\ \ge\ \dim V_{k-2}+k+1,\qquad
  \dim V_k\ \ge\ L(k+1),\qquad L(s)\coloneqq\left\lfloor (s+1)^2/4\right\rfloor .
 \tag{2}
\]
This is actual reverse row rank, independent of any prescribed chart. In particular \(d\ge L(r)\). The alternative sign of \(\Omega\) or the reflected coordinate gives the same rank statement.

Fix a physical prefix length \(j\) with \(1\le j\le d\), and write
\[
 n\coloneqq m-j,\qquad
 G(X)\coloneqq D(X)\prod_{i=1}^{j-1}(X-x_i).
\]
Assume \(n\ge1\) and these first \(j\) clocks do not coincide with either anchor. If \(d<\dim V_{r-2}+j\), there is a nonzero \(v\in V_{r-2}\) supported on that prefix, by intersection dimension. Its true model \(P\) has degree at most \(r-2\). It cannot be zero: (1) applied to \(v\) tests the prefix signed masses \(v_i D(x_i)\) against the whole \(\mathbb P_{\le m-1}\), and \(j\le m-1\) distinct non-anchor sites have full evaluation rank. Its literal right product \(vT\) is supported at most on the first \(j-1\) physical sites. The two rows therefore give the following finite necessary test, with no unknown tap or weight:
\[
 \ell(P G(X-x_j)Q)=0,\qquad
 \ell(P J(GQ))=0,
 \qquad Q\in\mathbb P_{\le n-1},\qquad 0\ne P\in\mathbb P_{\le r-2}.
 \tag{3}
\]
The first polynomial is a paid source at length \(r-2\) which vanishes at every site in the support of \(v\). The second identity uses the paid contact for \(vT\) at length \(r-1\) on \(GQ\), which vanishes on that shorter support, and the exact adjoint identity \(\ell((J^*P)GQ)=\ell(P J(GQ))\). In particular this proof makes no untested replacement of a numerical evaluation by \(JF\) when \(JF\) is not divisible by \(D\).

## 2. The prefix test fails generically

Suppose \(r-1\le 2n\) and \(j+1\ge n\). For fixed \(\alpha,a,\gamma\), the system (3) has no nonzero solution for a Zariski-open dense set of actual prefix tuples. This set is also dense in every real open prefix domain, and the same test holds over the real algebraic numbers. To prove it, specialise \(x_1,\ldots,x_{j-1}\) to distinct negative sites avoiding the anchors and let \(x_j\) tend to \(+\infty\), dividing the first group in (3) by \(-x_j\). The polynomial \(G\) now has \(j+1\) distinct strictly negative roots, and is positive on \([0,1]\). In the limiting equations, the first group is \(\ell(PGQ)=0\). Removing its multiple from the second and using exact integration by parts gives
\[
 R\coloneqq I_1 P,\qquad R(1)=0,\quad \deg R\le r-1\le 2n,\qquad
 \ell(G Q R)=\ell(G Q R')=0\quad(\deg Q\le n-1).       \tag{4}
\]
The following elementary sign lemma shows \(R=0\).

### Sign lemma

Let \(G\) have at least \(n\) distinct negative roots, all simple, and no other roots, with positive leading coefficient. Put \(\Theta\coloneqq G'/G\). The \(2n\)-dimensional rational function space
\[
             f=A+\Theta B,\qquad A,B\in\mathbb P_{\le n-1}
\]
has the property that a nonzero member has fewer than \(2n\) zeros, counted with multiplicity, on the nonnegative ray. Indeed, if \(H\) is a monic degree-\(2n\) factor composed of such zeros with multiplicity, then \(f/H\) has partial-fraction residues \(B(z)/H(z)\) at the negative roots \(z\) of \(G\), and decays as \(O(X^{-n-1})\) at infinity. The first \(n\) coefficients at infinity vanish. Against \(B\) this gives \(\sum_z B(z)^2/H(z)=0\). The denominators all have the same nonzero sign, so \(B\) is zero on all roots, hence identically zero. The remaining \(A\) must then be zero as well. Independence of \(A,\Theta B\) follows by taking residues (\(B\) would vanish at all roots). The argument also applies to prescribed zeros outside \([0,1]\).

If nonzero \(R\) satisfies (4), it has at most \(2n-1\) interior sign changes because its degree is at most \(2n\) and it vanishes at \(1\). Choose a nonzero \(f\) with \(2n-1\) distinct positive zeros, including those sign changes and completing the zero set with sites greater than one. Such a choice follows by the preceding dimension. All these zeros are simple by the multiplicity bound. Orient \(f\) so that \(fR\) is nonnegative and not identically zero on \([0,1]\).

Let \(H\) be the monic polynomial of these \(2n-1\) selected zeros, and \(\omega_z\coloneqq -1/H(z)>0\). The residues of \(f/H\) are now \(-\omega_z B(z)\), and its decay is \(O(X^{-n})\). Consequently \(B\) is orthogonal to every polynomial of degree at most \(n-2\) for the masses \(\omega_z\). The polynomial \(B\) is nonzero, since \(A\) alone could not have the selected zeros. Use that orthogonality with \((B(0)-B(Z))/(0-Z)\), a polynomial of degree at most \(n-2\), to obtain
\[
 B(0)\sum_z\frac{\omega_z B(z)}{-z}
       =\sum_z\frac{\omega_z B(z)^2}{-z}>0 .
\]
The residue formula, and \(-H(0)>0\), show that \(f(0)\) has the same nonzero sign as \(B(0)\). On the other hand, integration by parts in (4) with \(Q=B\) shows
\[
 \int_0^1 G f R = -G(0)R(0)B(0).
\]
The left side is positive; the right side is nonpositive because \(fR\ge0\) and \(f(0)\) has the sign of \(B(0)\). This contradiction proves the sign lemma. When \(n=1\), the orthogonality to degree at most \(-1\) is empty and the difference quotient of constant \(B\) is zero; the same proof applies.

Returning to (3), the limiting matrix has full column rank \(r-1\). Thus at least one \((r-1)\)-column minor of its original two groups is a nonzero polynomial in the prefix sites. This proves the stated generic claim. Moreover, for **each fixed** set of distinct negative sites \(x_1,\ldots,x_{j-1}\) avoiding the anchors, a minor has a nonzero leading coefficient as a polynomial in \(x_j\). Its degree is at most \(n\), since only the first \(n\) rows depend on \(x_j\) and each is affine. Hence there are at most \(n\) possible exceptional values of the next physical clock for that prefix. There is no need to know the locations or reality of the exceptional roots. Additional user-prescribed constraints on the clock grid are not assumed to meet the generic set.

## 3. Consequences and limits

For balanced odd \(p=2r+1\), \(m=r+1\), take \(j=\lceil r/2\rceil+1\). Then \(n=m-j=\lfloor r/2\rfloor\), \(r-1\le2n\), and there are enough roots of \(G\). At the minimum late width \(d=L(r)\), (2) gives \(d-\dim V_{r-2}\le L(r)-L(r-1)=\lceil r/2\rceil<j\). The cut therefore applies. **No choice of true weights and strict taps on a generic numerical prefix can pay even the lower-word contacts through \(r-1\) at that width.** A generic prefix requires at least \(L(r)+1\) late rows, even before the final feeder. Through \(20\), the odd targets with the actual two-sampler source hypothesis are \(9,11,13,15,17,19\); for even \(m\) use the canonical choice from [actual double-factor inputs](ACTUAL-DOUBLE.md). The result adds a new prefix rank obstruction even if previous independent restrictions on the opposite late suffix are met. It does not say that exceptional prefixes, or thicker banks, cannot work.

For balanced even \(p=2r\), use \(j=\lceil r/2\rceil\). The same generic test forces \(\dim V_{r-2}\le d-j\). At \(d=L(r)\) this forces \(\dim V_{r-2}=L(r-1)\) from the pure-double contacts alone. If the two complementary earlier-null heads described in Section 1 are also tested at length \(r-1\), then \(\dim V_{r-1}=L(r)\) and both parities in (2) saturate: every lower word space has its exact minimal rank and each \(N_k\), \(2\le k\le r-1\), consists exactly of \(V_{k-2}\Omega\). Thus on the generic prefix, any excess measured direction at the penultimate lower shelf already costs another late row. This even result is not a universal exclusion and does not assume that a minimum-rank lower dictionary can be realized.

All statements concern actual rooted contacts on the two-factor sources, not a model-only chart design. No target's unrestricted upper or lower bound changes here.
