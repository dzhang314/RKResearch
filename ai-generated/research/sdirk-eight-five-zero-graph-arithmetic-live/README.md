# Complete live arithmetic-front graph exclusion in characteristic zero

Consider a strict ten-stage SDIRK tableau of order at least eight over a characteristic-zero field, with exactly five physical zeros of the quadratic residual \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume genuine quadratic graph support, no live off-zero row, first physical zero at row 4 with the literal arithmetic front, and live physical row 8.

**Result.** This chart is impossible over every characteristic-zero field. Together with the earlier pure-support and graph exclusions, this proves that **any characteristic-zero ten-stage candidate with exactly five physical quadratic zeros must have a live off-zero row**. This does not rule out exactly five physical zeros with active off-zero rows, or independently change a global stage bound.

## 1. Projection without losing the reflected orientation

The ordinary measure consists of five distinct live zero clocks. As in the [leading-drop companion](../sdirk-eight-five-zero-graph-arithmetic-live-leading/README.md), the actual rear ordinary triple in physical order is
\[
\begin{aligned}
\text{arithmetic: }&(m-r,m,m+r), & \gamma&=1-m-r,\\
\text{star: }&(m+r,m-r,(1+m)/2), & \gamma&=(1-m)/2 .
\end{aligned}
\]
The signed \(r\) remains a variable in both phases. Mask these three known nodes and take the ordinary \(3\)-by-\(3\) Hankel determinant; it vanishes. In both phases its polynomial in \(r\) has only even powers. In arithmetic remove the factor \(2m-1\) only after putting its entire \(m=1/2\) line in the exceptional companion. Write the primitive remainder as \(\ell(m)r^6+s_4(m)r^4+s_2(m)r^2+s_0(m)\); the star does not have this prefactor. The \(\ell=0\) fibers have also been checked in the leading-drop companion and are not dropped by a gcd heuristic.

For \(\ell\ne0\), set \(R=\ell r\) and \(E=R^2\). The rear phase is an exact monic cubic in \(E\) followed by \(R^2=E\); the signed root keeps the real chronology, even if the two orientations belong to different algebraic extensions. Let \(\Delta\) be the \(2\)-by-\(2\) Hankel pivot from the masked moments multiplied by the common scalar \(\ell^3\). With two unknown ordinary clocks this pivot is structurally nonzero. Scale the clocks by \(d=\ell\Delta\), and set \(g=d\gamma\). If \(N_\ell,N_q\) are the linear and constant Cramer numerators, the two early clocks \(a,b\) in this scaling satisfy
\[
 Q_a(X)=X^2+\ell N_\ell X+\ell^2\Delta N_q=0,\qquad
 b=-\ell N_\ell-a.
\]
The third chronological zero is the actual physical row 8, so its scaled value is known once \(m,R\) are given. All orders of the early pair are retained.

The [arithmetic supported-pencil gates](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#2-three-supported-equations-in-the-same-arithmetic-pencil) apply with these clock values, endpoint \(d\), and diagonal \(g\), giving \(X,Y\) in the regular case or \(D_0,A_N,B_N\) in the singular case. The projection code evaluates them in a free rank-12 monic tower (cubic \(E\), quadratic \(R\), quadratic \(a\)), and uses successive multiplication norms to eliminate \(a,R,E\). These determinant norms vanish whenever the original respective gates have an actual root. Uniform content divisions use only factors of \(\ell\), which is already nonzero in this part of the argument.

| Rear | Exact regular norm gcd degree | Exact singular norm gcd degree | Non-leading squarefree factor degrees |
| --- | ---: | ---: | --- |
| Arithmetic | 2670 | 1170 | 1, 4, 4, 4, 8, 16 |
| Star | 3378 | 1476 | 1, 1, 4, 4, 9, 18 |

Both gcds have the same non-leading support in each phase. The arithmetic linear factor is its already treated \(m=1/2\) line. The factor ledger consists of exact rational polynomials and is checked against the projected gcds. No other projection factor, including ones that might be caused by another \(R\) fiber at the same \(m\), is stripped globally.

## 2. Local geometric fibers

At each remaining irreducible \(m\)-factor, reconstruct the actual signed gap polynomial, the degree-two ordinary Cramer system, and both physical orientations of \(a,b\) over the exact quotient field. Compute the univariate gcd in the signed gap with the appropriate supported-gate norms (over \(a\) only). In particular, these calculations do **not** rule out \(m\) just because some other reflected gap in its fiber has a bad pivot. The exact gap gcds before and after local guard removal are verified for both regular and singular pencils. Every nonempty removed support is one of:

| Rear | Degree of \(m\)-factor (in ledger order) | Gap gcd degree before guards | Actual guard removing the whole gcd |
| --- | ---: | ---: | --- |
| Arithmetic | 16 | 2 | Early ordinary clock collision |
| Arithmetic | 4 | 6 | A Gaussian early clock |
| Arithmetic | 4 | 2 | A Gaussian early clock |
| Arithmetic | 4 | 1 | Common diagonal zero |
| Arithmetic | 8 | 2 | Ordinary Hankel pivot zero |
| Star | 1 (\(m=1\)) | 6 | Common diagonal zero |
| Star | 1 (\(m=1/2\)) | 4 | A Gaussian early clock |
| Star | 4 | 2 | A Gaussian early clock |
| Star | 4 | 6 | A Gaussian early clock |
| Star | 9 | 2 | Ordinary Hankel pivot zero |
| Star | 18 | 2 | Early ordinary clock collision |

The Gaussian norm is again just over the two early clocks at the **same signed gap**. At any actual candidate both clocks are live and distinct, so the [five-site ordinary Gauss guard](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md#1-literal-clock-data-and-the-ordinary-cubic) makes both evaluations nonzero. The checked norm exclusions therefore apply over every extension of the corresponding rational quotient field, without an ordering or a real-root assumption. The residual gcd in every exact fiber is constant.

## 3. Full no-active-off consequence

The [support census](../sdirk-eight-five-zero-support-rank/README.md) forces the unique supported quadratic, either pure or graph. With no live off-zero row:

- The pure case with four ordinary sites is impossible by the [four-ordinary proof](../sdirk-eight-five-zero-pure-four-ordinary/README.md). With five distinct live zeros, the [silent eighth](../sdirk-eight-five-zero-pure-silent-eighth/README.md) and [live eighth](../sdirk-eight-five-zero-pure-live-eighth/README.md) exclude it.
- In the graph case [four ordinary sites](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md) and [only four distinct off clocks](../sdirk-eight-five-zero-graph-distinct-off/README.md) are impossible. The [long front proof](../sdirk-eight-five-zero-graph-four-off/README.md) leaves the first physical zero at row 3 or 4. Row 3 is excluded with [live](../sdirk-eight-five-zero-graph-third-live-eighth/README.md) or [silent](../sdirk-eight-five-zero-graph-third-silent-eighth/README.md) row 8. At row 4 the [star front](../sdirk-eight-five-zero-graph-star-front/README.md) and the [arithmetic front with silent row 8](../sdirk-eight-five-zero-graph-arithmetic-silent/README.md) are excluded. The exceptional live families and the exact local check in this packet finish the remaining arithmetic front.

Replay `python check_projection.py arith` and `python check_projection.py star` with Python-flint 0.8; each exact projection takes roughly one minute. Replay `python check_fibers.py arith` and `python check_fibers.py star` with SymPy 1.14 to check all local quotient-field calculations. The supported scalar algebra is the same as the silent packet; the symbolic norms and chart classification are mathematical source proofs and exact replays, not a single native `HasOrder` theorem.
