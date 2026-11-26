# A two-stage growth tax for complete RK moment seeds

Notes-only addendum to
\`FIXED-SEED.md\`.
No new numerical or repository work. This states exactly what the fixed-seed argument needs at other orders.

Let a strictly explicit seed have normalized endpoint 1 and a genuine initial origin. Fix a lower ordinary-tree order \(g\) and an integer \(k\ge1\) with \(g\ge k+5\). Suppose its **complete** genuine scalar duals through sizes \(g\) and \(g+1\) are respectively
\[
       \operatorname{span}(E_0,\mu_0,\ldots,\mu_k),\qquad
       \operatorname{span}(E_0,\mu_0,\ldots,\mu_{k-1}),
       \qquad
       \mu_j(f)\coloneqq\int_0^1 x^j f(x)\,dx .
\]
Here a true coefficient row evaluates the scalar derivative of every ordinary rooted tree, not only a selected monomial. Assume each actual zero coefficient row through size \(g\) has zero total on each individual clock fibre. This last assumption is automatic when the seed has at most \(g\) distinct clocks, by testing the \(g\) pure bush powers. It may hold on a larger clock set, as certified for the fixed gathered Stepanov seed.

Then among the next **two arbitrary strict rows**, at most one independent true size-\((g+1)\) scalar direction can be gained. Any first-row gain is precisely the previously unavailable \(E_1\). Thus after \(N\ge2\) added stages the new size-\((g+1)\) scalar dimension is at most \(k+N\). This concerns the two entire actual scalar duals; a merely explicit list of some genuine moments is not enough.

For proof, let \(Q\) be the scalar kernel at size \(g\). Its primitives \(P=Jq\) have a double zero at 0, a simple zero at 1, and \(k\) zero moments against \(1,x,\ldots,x^{k-1}\), by integration by parts. Their degree is at most \(g\), so \(d\coloneqq\dim Q=g-k-2\). At a trial new clock \(r\), genuine upper \(F\) forces both \(FJ|_Q=0\) and \(F((x-r)\cdot)|_Q=0\) by the two literal pullbacks. To intersect \(JQ\) and \((x-r)Q\), write \(P_1=(x-r)P_2'\). This requires one extra zero on \(P_2\) at each noncoincident endpoint and no extra zero at the coincident endpoint. The original \(k\) moments suffice for \(P_1\)'s moments since integrating \(x^j(x-r)P_2'\) differentiates a polynomial of degree \(j+1\). The \(k\) conditions on the smaller polynomial factor are independent by positivity of the endpoint weight and the Gram on monomials. Therefore the intersection dimensions are \(d-2\) off the two endpoints, and \(d-1\) at them. The allowable upper space is exactly the earlier \((k+1)\)-dimensional upper library off endpoints. At 0 the extra form is \(E'_0\), ruled out because its clock pullback would truly represent \(E_0\) but must vanish on the whole coincident fibre. Old zero rows cannot change that fibre's total. At 1 the extra form is \(E_1\).

If \(E_1\) is bought, it increases the earlier lower dual precisely by that direction and does not introduce a new lower zero row (eliminate its nonzero new physical slot). Its new coefficient representative has aggregate one at 1: multiply by \(C-I\), obtain an old zero row, use the zero-fibre assumption, and use the constant test. Repeating the intersection argument with both endpoint multiplicities now double gives only the matching first derivative as a formal extra at either endpoint. Neither can be physically purchased, by the fibre-sum obstruction. The noncoincident upper directions are all already available. Thus the first two stages make at most one gain. Afterwards every literal row adds at most one, giving the bound.

The scope is not restricted to a Cauchy construction. To escape it while retaining the same complete earlier moment duals, a new seed can provide a lower zero row with a nonzero fibre sum; to use a repeated lift this must pay the **whole** coincident-slot vector and live on admissible local support, as in the companion result. Alternatively expand the earlier true lower dual by a nonmoment observation. Upper-bound conclusions need further exact constructions.
