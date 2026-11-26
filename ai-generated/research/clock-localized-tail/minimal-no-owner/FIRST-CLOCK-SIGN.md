# The two-source screen already forces a negative first clock

This strengthens the nonnegative case of the [pointwise projection theorem](ONE-MARK.md). It does not use the sign estimate for a single projected Laguerre polynomial.

In the balanced minimum direct geometry, let \(\gamma<0\) and let \(\alpha=\gamma\lambda\) be **any** actual chosen final normalized Laguerre root of the canonical early cache, of degree \(h=m-1\ge2\). The first physical late row must vanish on every true projected primitive (4) in the companion note. The explicit cancellation follows from the final coefficient residual \(U\coloneqq W_{h-2}-cW_{h-1}\), where \(c\coloneqq W_{h-2}(\alpha)/W_{h-1}(\alpha)\). Here \(\xi\coloneqq(h\lambda-1)/(h-1)\). With the physical normalization of the \(W_j\), the Laguerre recurrence gives
\[
 JU+\frac{W_{h+1}}{\gamma^2h^2(h-1)}
   =\frac{(X-\gamma\xi)W_h(X)}{\gamma^2h^2(h-1)}.
\]
Indeed \(JW_j=W_{j+1}/(j+1)\), and the recurrence at \(\alpha\) gives \(c=(\alpha-\gamma(2h-1))/\bigl(\gamma^2(h-1)^2\bigr)\). Substituting these expressions leaves the displayed multiple of \(W_h\). Its value at \(\alpha\) is zero, so the same linear combination cancels the two Legendre corrections.

At the first physical late abscissa the displayed polynomial must vanish, whether or not the shifted Legendre polynomial vanishes there. Only the denominator \({\cal L}_m(\alpha)\) was used in the correction, and it is nonzero for \(\alpha<0\).

All roots of physical \(W_h\) are negative. Also every normalized Laguerre root \(\lambda_j\) satisfies \(\lambda_j>1/h\): using the factorization of \(\mathscr L_h\) normalized at zero, \(\sum_j1/\lambda_j=-\mathscr L_h'(0)/\mathscr L_h(0)=h\). The \(h\ge2\) terms are strictly positive, so each individual reciprocal is strictly less than the sum. Consequently \(\xi>0\) for every possible chosen \(\lambda\), and \(\gamma\xi<0\). The necessary first clock is therefore negative for **every** negative diagonal, not just for \(g\ge1/(m+1)\) or for the extremal chosen \(\lambda\).

Together with the [prime-degree](NEGATIVE-ANCHOR.md) and [prime-interval](PRIME-INTERVAL.md) exclusions, this rules out the balanced canonical minimum-width constructions at orders \(12,16,18,20\) for all real negative diagonals. It does not change the unrestricted SDIRK stage table or cover positive diagonals.
