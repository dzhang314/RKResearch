# Shared doubled endpoints: one extra D cannot oppose the two-singleton star

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, every physical quadratic residual nonzero, exactly seven distinct clocks and a genuinely quadratic singleton graph. The two actual endpoints share a D (doubled) label. Orient forward a prefix with exactly one later D and one later S (singleton), and suppose the other actual prefix is D,S,S with a literal star third tap. This case is impossible. The reverse arithmetic D,S,S remains outside this packet; no numerical stage interval changes. Signed weights are allowed.

Normalize the diagonal to one. The shared D label is \(t=x-1=0\) and \(\ell=2\). Let \(d\) be the extra forward D label and \(e\) the remaining noncentral D label. The [odd projected quintic and graph census](../sdirk-eight-all-dirty-seven-quadratic-shared-one-extra-d/README.md) says the graph is centered-even if \(e=-d\), including Hermite roots, or \(R=rW,\ W=(t+d)(t+e)\) if \(e\ne-d\), with \(35d^2e^2-21(d^2+e^2)+15=0\). A genuine reverse star has two distinct S clocks with equal residual; in original centered coordinates their sum is \(-2\). Hence its graph axis is \(-1\), excluding centered-even or Hermite shape and giving \(d+e=2\) in the split shape. For \(S=(d-1)^2\), \(W=(t+1)^2-S\). The exact polynomial for \(d\) is
\[
  35[d(2-d)]^2+42d(2-d)-69=35d^4-140d^3+98d^2+84d-69=0,
\]
an irreducible quartic. These formulas do not choose a square-root sign.

The forward pair data are A2, A3 or either star order as in the linked census. In either forward star order the nominal singleton label would be \(2-d=e\), a doubled clock, so that phase is impossible. Retain both arithmetic orders. Their known \(g_D\) at \(d\) and \(g_f\) at the forward singleton \(\sigma\) give \(r=g_f/W(\sigma)\), nonzero. Write \(\beta=B\lambda=-4L_4(0)\) by the actual terminal overlap, where \(\lambda\) converts reverse to original residuals.

For the reverse star gap \(v\) put \(X=(v-1)^2\); its two original singleton labels are \(-1\pm\sqrt X\), with known reverse normalized residue \(\tau=(2-X)/2\). Their actual graph value gives \(\lambda\tau=r(X-S)\). This does not require either square root to be real. Let \(C=A_2+B R\) and \(M=\tau\lambda C\), a quadratic in \(t\) whose three known values are affine polynomials in \(X\):
\[
 \begin{split}
 M(0)&=-\beta[\tau+r(X-S)]/2+\beta r\tau W(0),\\
 M(d)&=r(X-S)L_4(d)/g_D+\beta\tau[rW(d)-g_D],\\
 M(\sigma)&=r(X-S)L_4(\sigma)/g_f .
 \end{split}
\]
The first uses the actual residual sum at the doubled endpoint, the second uses the known forward D equation \(U=0\), and the last is the true forward singleton equation. Their clocks are pairwise distinct, so these pay the entire quadratic \(M\). Each reverse singleton has original residual \(\lambda\tau\), so its actual equation is \(L_4-M=0\). Reduce \(L_4-M\) modulo \((t+1)^2-X\); both coefficients of the remainder must vanish. Their exact gcd in \(X\) is already one for both A2 and A3 in the quartic field. No affine coefficient, ordering, normalized trace, or finite-characteristic transfer is needed.

Run `python check_shared_mixed_star.py` with SymPy 1.14 and python-flint 0.8 (it imports the sibling `prefix_scalars.py`). This packet reuses the earlier staged scalar Lean source and adds no new native or end-to-end build.
