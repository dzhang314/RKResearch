# Two same-diagonal endpoint contrasts repair two rooted grades

Let \(A,\mathbf b\) be a strict SDIRK tableau of ordinary order at least \(d\ge2\), over a field of characteristic zero, with common nonzero diagonal \(\gamma\). Assume all its trees through size \(d+2\) already have correct output **except possibly**:
1. unary roots at sizes \(d+1\) and \(d+2\);
2. trees \([v]\#[\bullet]\) with \(|v|=d\), at size \(d+2\).

These are specific partial conditions, not a claim that ordinary order \(d\) gives them. If it has two distinct actual stage clocks \(x,y\) with \(y=1-\gamma\), the tableau can be extended to order at least \(d+2\) in at most two physical rows. The old stage equations are unchanged; the scalar aggregate weight at every clock remains unchanged. If there are two distinct clocks but no specified one at \(1-\gamma\), at most three new rows at existing clocks suffice. The construction is rational when the input is rational.

Write \(C\coloneqq\operatorname{diag}(A\mathbf1)\) and use row coordinates for the output, for purposes of matrix multiplication. Define the exact needed correction and the two actual covectors by
\[
 \epsilon_t\coloneqq \frac1{t!}-\mathbf b\cdot\boldsymbol\Phi_t(A),
 \qquad
 L\coloneqq \mathbf b(I-C-A),\qquad
 M\coloneqq \mathbf b\bigl((I-C^2)/2-CA\bigr).
\]
For \(g_t(X)\coloneqq |t|X^{|t|-1}/t!\) the formal actions of unary extension and attachment of a new leaf are \(J\) and multiplication by \(X\), respectively. The identities \(I(Jf)=I((1-X)f)\) and \(I(XJf)=I((1-X^2)f/2)\) give
\[
 \begin{aligned}
 L\boldsymbol\Phi_u&=\epsilon_{[u]}-\epsilon_u+\epsilon_{u\#[\bullet]},\\
 M\boldsymbol\Phi_u&=\epsilon_{[u]\#[\bullet]}-\epsilon_u/2+
                         \epsilon_{u\#[\bullet]\#[\bullet]}/2 .
 \end{aligned}
\]
For \(|u|\le d\) the last two summands of the second line are zero: the latter has at least three root children when \(|u|=d\), since \(d\ge2\). In particular both \(L\) and \(M\) vanish on actual old tree columns of size at most \(d-1\). On size \(d\), they are the required corrections on \([u]\) and \([u]\#[\bullet]\), respectively. No extension of an abstract functional from an unverified tree relation is needed.

## Physical receivers

At old stages \(i_1,i_2\) with clocks \(x_1=x,x_2=y\), append two rows with their same prestates and literal diagonal \(\gamma\), apart from the added strict feeds described here. The prestate of an original row excludes its diagonal. Define two old-stage rows and one cross tap by
\[
 \ell_1\coloneqq(M-yL)/(x-y),\qquad
 \ell_2\coloneqq(xL-M)/(x-y),\qquad
 \kappa\coloneqq -(x-y).
\]
The first new row adds the old feed \(\ell_1\). The second adds old feed \(\ell_2\) and the strict tap \(\kappa\) on the difference between the first new derivative and its old reference derivative. This is two literal entries to preceding stages, not an implicit dependency. Neither clock changes, since \(\ell_1,\ell_2\) annihilate the old constant tree column, and the cross difference has zero row mass. Give each new row output weight \(+1\) and subtract \(1\) from its corresponding old weight.

Let \(\delta^\alpha_t\) denote the new-minus-reference coordinate on tree \(t\), for \(\alpha=1,2\). Directly from the row equation,
\[
 \delta^\alpha_{[u]}
   =\ell_\alpha\boldsymbol\Phi_u+\gamma\delta^\alpha_u+
              \mathbf1_{\alpha=2}\kappa\,\delta^1_u .
\]
The deltas vanish through size \(d\). In a rooted product, a changed root factor first costs a child of size \(d\), so two changed factors would require size \(2d+1>d+2\). At size \(d+1\) the only change is the unary \(L\boldsymbol\Phi_u\). At size \(d+2\) a changed non-unary root can only have one child of size \(d\) and another child which is a leaf. The unaffected leaf factor is its old clock, so the total change is \(M\boldsymbol\Phi_u\). All untouched trees stay untouched.

For a size-\((d+2)\) unary tree \([u]\), the direct change is \(L\boldsymbol\Phi_u\). If \(u=[v]\) with \(|v|=d\), the additional echo down the unary path is
\[
   (\gamma L+\kappa\ell_1)\boldsymbol\Phi_v=(L-M)\boldsymbol\Phi_v
\]
using \(y=1-\gamma\). It is precisely \(\epsilon_u-\epsilon_{u\#[\bullet]}\). If \(u\) is not unary, both of those corrections are zero by the hypothesis and there is no echo. The first covector identity now gives the required \(\epsilon_{[u]}\). This verifies all rooted conditions, not just the first two row identities on clock-only trees.

For arbitrary distinct \(x,y\), do not make the cross tap in the second row. Instead append a third old-prestate clone at either clock, with strict differences from the first two new rows weighted by \(1-\gamma-x\) and \(1-\gamma-y\). Give it output correction \(+1\) minus its old reference. Its first contribution is at size \(d+2\), on a double unary root, where it adds \(((1-\gamma)L-M)\boldsymbol\Phi_v\). The same verification applies. If \(L\) already annihilates size-\(d\) columns (for example the seed is of order \(d+1\)), the two-row version works at *any* distinct clocks with the stated cross tap: the difference between its echo and \(L-M\) is \((x_2+\gamma-1)L\), zero on every needed column.

A further sufficient case uses only one appended row: if there is an old reference at \(1-\gamma\) and \(M=(1-\gamma)L\) on the actual size-\(d\) columns, use the sole contrast \(L\) there. The leaf decoration is then correct, and the diagonal echo \(\gamma L\) already equals \(L-M\) on those columns.

The scalar quadrature is unchanged at all degrees in every version. In particular an original nonzero bush residual at size \(d+3\) supplies an exact next-order witness. An original bush residual at sizes \(d+1\) or \(d+2\) cannot be corrected, and excludes the hypothesis. Reweighting the old rows is possible only if a new old output meets the partial conditions; if its paid old columns through \(d\) span the entire stage space, the order-\(d\) old output is unique and cannot be reweighted.
