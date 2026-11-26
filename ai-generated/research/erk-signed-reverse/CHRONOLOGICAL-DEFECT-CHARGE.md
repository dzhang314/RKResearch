# A forward defect charge independent of the seed clocks

Let \(A\) be strictly lower triangular over a field with the relevant small integers invertible. For tree size \(k\), let \(F_k\) be the span of the actual columns of combinations through that size whose exact polynomial profiles sum to zero. This definition is meaningful on any actual prefix without a numerical-to-polynomial map. Suppose either that an ordinary output pays order \(r\ge3\) or that a dense derivative decoder pays through size \(r\ge3\). Then
\[
                 \dim F_k\ge k-2\qquad(3\le k\le r).
\tag{1}
\]
A dense derivative ERK chart through size \(m\ge3\) therefore needs at least \(2m-2\) rows. In particular the eight-row construction is minimal at size five, and the six-row chart in its prefix is minimal at size four.

To prove (1), put \(\mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2\), where \(\mathbf c\coloneqq A\mathbf1\), and let \(C\) multiply by \(\mathbf c\) coordinatewise. The first nonzero clock has zero \(A\mathbf c\) entry, so \(\mathbf q\) is a nonzero element of \(F_3\). The requisite nonzero clock exists under either hypothesis, already at size two. Unary extension and adding a root leaf give \(AF_k,CF_k\subset F_{k+1}\).

If \(F_k=F_{k+1}\), let bars denote the quotient by this now jointly invariant space. The tails of the chronological coordinate flag descend to the quotient. The operator \(\bar A\) maps each of these tails into the next, and \(\bar C\) preserves each tail. Since \(\overline{\mathbf c}\) is in the image of \(\bar C\), applying \(\bar C\) to it does not increase its tail index: a polynomial in \(C\) inverts \(C\) on the nonzero clock sector and preserves all the flags. But \(\mathbf q\in F_k\), so
\[
                   \bar A\overline{\mathbf c}=\bar C\overline{\mathbf c}/2.
\]
If \(\overline{\mathbf c}\ne0\), its last tail would include the left side in the next tail and not the right side. Thus \(\mathbf c\in F_k\). Under the ordinary hypothesis its exact output is \(1/2\), while the output annihilates \(F_k\); under the dense hypothesis its exact profile is \(X\), while the decoder annihilates \(F_k\). Both are contradictions. Starting with the nonzero \(F_3\) proves (1), and a full dense chart has at least \(m+\dim F_m\) independent directions because its clock powers map to the monomial basis.

For a nonzero ring with the requisite factorial invertible, the same numerical bounds follow by reduction to a residue field. In the dense size-\(m\) case \((m-1)!\) is enough for the derivative profiles; the ordinary cleared size-\(r\) hypothesis itself forces \(r!\) to be a unit by the tall tree.

There is also an exact seed-specific accounting that adds any old physically unused coordinates. If the fixed seed has \(s_0\) rows and \(E_m\) is the span through size \(m\) restricted to them, its available linear model information has dimension \(\dim E_m-\dim F_m\). Indeed the rank of the paired span of actual seed columns and exact polynomials is \(m+\dim F_m\), by projecting to the polynomials; projecting to the actual columns shows that the dimension of old physically zero polynomial relations is \(m+\dim F_m-\dim E_m\). Adding one stage can remove at most one such relation. In particular any dense size-\(m\) continuation with no changes to the seed needs
\[
 s\ge s_0+m+\dim F_m-\dim E_m\ge m+\dim F_m.
\tag{2}
\]
On an unchanged ERK seed of ordinary order \(r\), equation (1) also shows that every such continuation pays at least \(\min(m,r)-2\) old pure-defect directions if \(\min(m,r)\ge3\). This conclusion needs no assumption about distinct clocks, adjacent strict links, or any positivity. It is a dense preparation bound, not an unrestricted ordinary-output stage bound.
