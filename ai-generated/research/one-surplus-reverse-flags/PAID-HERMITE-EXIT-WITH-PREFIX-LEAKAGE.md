# Paid Hermite exits modulo a clock-saturated cover

This is a weighted chronological rank estimate. It generalizes the line-only Hermite count by measuring exactly how much of the local clock cover is missing from the already-paid input space on the prefix being tested.

Let \(N\) be lower triangular in physical chronology, let \(Y=\operatorname{diag}(\mathbf y)\), and let \(\mathbf v\) be the scalar base, such as the reversed output coefficients of a Runge–Kutta tableau. Suppose \(M_j\) is a true one-mark zero-density flag, so that
\[
 NM_j, YM_j\subseteq M_{j+1},\qquad
 N\bigl(\mathbf v\odot P(\mathbf y)\bigr)
          -\mathbf v\odot (JP)(\mathbf y)\in M_{j+1}
                              \qquad(\deg P\le j),
\]
where \(J(X^k)\coloneqq X^{k+1}/(k+1)\). The corresponding rule applies at grade \(j-1\). Use these hypotheses only at their stated cutoffs. In a terminal-zero subflag the displayed errors and transport must belong to that subflag.

Fix a \(Y\)-invariant cover \(W\) containing \(M_j+YM_j\); it need not be pure or contained in \(M_{j+1}\). On clock \(x\), let \(\mathbf v_x\) denote the part of \(\mathbf v\) supported at that clock. If the prefix of \(\mathbf v_x\) eventually fails to agree with any vector of \(W\) on that fibre, record the first physical index at which it fails. Choose a row \(\lambda_x\) supported on that prefix of the fibre, killing \(W\) and normalized by \(\lambda_x\mathbf v_x=1\). Such a row exists by linear duality on the restricted coordinate space. Its entry at the last physical pivot is nonzero by the choice of the first failure.

Consider the first \(d\) detected nonzero clocks, in order of their first failures, and let \(I\) be the physical prefix through the last of them. Set
\[
 \ell_I\coloneqq\dim(\pi_I W/\pi_I M_j),
\]
where \(\pi_I\) is restriction to actual coordinates. This is observed prefix leakage, not the ambient dimension of \(W/M_j\).

**Outgoing.** If \(2d\le j\), the \(d\) literal detector rows have rank at least \((d-\ell_I)_+\) on
\[
                M_{j+1}/(M_{j+1}\cap W).
\tag{5}
\]
**Incoming.** If \(2d+1\le j\), their compositions \(\lambda_xN\) have rank at least \((d-\ell_I)_+\) on \(M_j/M_{j-1}\).

For the outgoing proof, let \(\Lambda\) span the chosen rows. They have disjoint fibre supports, so \(\dim\Lambda=d\). A combination \(\lambda\in\Lambda\) killing \(M_{j+1}\) has \(\lambda N\) killing \(M_j\). By chronology \(\lambda N\) is supported in \(I\), so its restriction to \(W\) gives a readout on \(\pi_I W/\pi_I M_j\). We claim this map is injective on the kernel. Suppose instead that a nonzero such \(\lambda\) also satisfies \(\lambda N W=0\). At any fibre not yet detected by the last nonzero pivot of this combination, the prefix of its scalar base matches \(W\), so \(\lambda N\mathbf v_x=0\) there. Its pooled masses are therefore confined to the earlier detected fibres and the current one, with the origin possibly among them.

Let \(u\ne0\) be the clock of the combination's last nonzero detector. Put
\[
 B(X)\coloneqq X^2\prod_{x\text{ earlier nonzero detected}}(X-x)^2,
 \qquad
 S(X)\coloneqq B(X)\left(1-\frac{B'(u)}{B(u)}(X-u)\right).
\]
The product includes all detections preceding this pivot, not just those with nonzero coefficients in \(\lambda\). Then \(S(0)=0\), it and its derivative vanish at previous nonzero detected clocks, and \(S'(u)=0\), \(S(u)\ne0\). The largest possible degree is \(2d+1\). Thus \(\lambda N(\mathbf v\odot S'(\mathbf y))=0\), whereas \(\lambda(\mathbf v\odot S(\mathbf y))\ne0\). The primitive discrepancy is paid in \(M_{j+1}\), a contradiction. This proves injectivity and then (5), since all detectors kill \(W\).

For the incoming proof the kernel consists of combinations with \(\lambda N\) killing \(M_j\). Its restriction to the same leakage quotient is injective by the same calculation, because \(\lambda\) kills \(M_j\subseteq W\) and this time the primitive discrepancy is paid in \(M_j\). The transported detectors kill \(M_{j-1}\) by \(NM_{j-1}\subseteq M_j\).

All divisions are nonzero fibre-value divisions or paid primitive factors. There is no assertion about individual weight signs, and a row of weight zero need not be removed. If the origin is not detected by the final chosen prefix, its square in \(B\) may be replaced by a single factor. If the last chosen pivot is physically explicit, for that last combination \(\lambda N\) has strict earlier support, so one can instead use \(S=B\) there. Either improvement can save one degree; combinations ending at an earlier pivot retain the default bound.

## Single-head form and a one-surplus consequence

Suppose
\[
 M_j=U\oplus \mathbf w\mathcal P_{r-1}(Y)
]
with \(U\) clock invariant. Take \(W\) to be its clock-saturated cover, adjoining all actual fibre parts \(\mathbf w_x\) of the single head. Let \(h_I\) be the number of distinct labels on which the truncated head fibre is nonzero modulo \(\pi_I U\). Then
\[
 \ell_I=(h_I-r)_+ .
\tag{6}
\]
Indeed the independent visible head fibres are supported on disjoint actual labels; the already-paid powers give the Vandermonde rank \(\min(h_I,r)\).

If the outgoing step allows at most one independent direction beyond \(M_j+YM_j\), (5) gives \(\ell_I\ge d-1\) for \(d\ge2\). Hence the \(d\)-th fresh nonzero detector already has at least \(r+d-1\) visible head labels on its prefix. Moreover there are at least
\[
                  \dim\pi_I U+r+2d-1
]
physical rows on that prefix. This uses the \(d\) independent detector rows annihilating the prefix cover, in addition to its dimensions. In particular two fresh detectors beyond a fully paid prefix force two extra directions, and three beyond a prefix leaking one dimension still force two. For an outgoing noninvariant unit step (no extra direction), replace \(d-1\) by \(d\). The incoming estimate instead compares to the total actual gain \(\dim M_j-\dim M_{j-1}\): if that gain is \(a\), it gives \(\ell_I\ge d-a\) under the one-grade stricter budget. It does not count beyond the incoming clock extension unless the transported detectors are also checked to annihilate \(YM_{j-1}\).

This is a conditional certificate in actual coordinates. It does not infer the number of fresh detectors just from the head count. For example a nonzero pooled scalar mass makes its fibre detectable whenever \(W\) has zero pooled mass there, but a nonpure head cover can already contain that scalar fibre. Then no additional Hermite detector is available at that label. The leakage term is likewise an actual cut rank, not merely a count of global unrepresented polynomials.
