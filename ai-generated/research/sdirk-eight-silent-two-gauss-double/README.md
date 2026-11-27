# Closing the repeated Gauss-clock chart among eight active stages

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, consider the case with two individually invisible off-zero stages, both at a single physical clock, both with the same quadratic residual, and all eight zero-residual stages active. In the remaining non-midpoint branch with \(r_2=1\), the [high-active packet](../sdirk-eight-silent-two-high/README.md) shows that if there are seven distinct active clocks, the sole doubled clock \(r\) is Gauss. This note closes that entire branch, including when the second invisible stage is physical eight. The only remaining two-invisible equal-tag branch has **eight distinct active physical clocks** and a non-midpoint diagonal. No unconditional change to **10–11**.

Use \(x=1-\gamma\) and \(u=(x-c_9)/\gamma\ne0\). For \(y=c_9\) or \(c_8\) when the corresponding row is active, let \(k_y\) be the actual reverse normalized quadratic residual divided by its first value. The penultimate value is \(k=1+2u-u^2\). From the supported pure reverse row,
\[
 (x-\gamma)h_y=k_y(y-\gamma)h_{10}.
\]
There is no normalization by the silent weights. In the Gauss-double chart, all \(h_y\) at singleton clocks equal a common nonzero scalar times \(P(y)\), where \(P=L_4/(X-r)\). The root \(r\) lies on the affine \(Q\) interpolated from \(L_4(a)/h_a,L_4(b)/h_b\). Its explicit diagonal projection has factor degrees \(4,4,12\) in each phase. Exact gcds of those factors with \(Q(x),Q(\gamma),L_4(\gamma)\) show \(x\ne r\), \(\gamma\ne r\), and \(x,\gamma\) non-Gauss, so the terminal row is always singleton.

At a singleton ninth, the exact polynomial
\[
 F_9(u)=(x-\gamma)P(x-\gamma u)-k(x-\gamma u-\gamma)P(x)
\]
must vanish. It has an exact extraneous factor \(u\), removed before reduction. For an active physical eighth stage, its clock is \(d=x-\gamma(2-u)\) in the star phase or \(d=x-2\gamma u\) in the arithmetic phase. In star, \(k_d=k\). In arithmetic, with \(H=-2+u+4u^2-u^3\), one has
\[
 H k_d=(1+4u-4u^2)H+4u^2(3u-2).
\]
This is the literal reverse third-row identity, with no new division by \(H\). At a singleton eighth the corresponding denominator-cleared polynomial is \(F_8(u)\).

The three active-eighth cases exhaust the literal positions:
* Both ninth and eighth are singleton. The two required polynomials \(F_9/u,F_8\) are coprime in each reduced field. The \(F_9/u\) quadratic retains degree two in all components (a leading unit), so the unit lifts in its fixed monic basis. There is no modular-only deletion of a coincident root.
* Ninth equals \(r\); eighth is necessarily singleton since the active reverse triple has distinct clocks. Then \(u=(x-r)/\gamma\) is fixed and \(F_8\) evaluates to a unit.
* Eighth equals \(r\); ninth is necessarily singleton. The star/arithmetic incidence gives \(u=2-(x-r)/\gamma\) or \(u=(x-r)/(2\gamma)\). At either fixed value \(F_9\) evaluates to a unit. No value of \(h\) at the doubled clock was set to \(P(r)\).

If the physical eighth stage is silent it is the second invisible, at \(\gamma\). The actual two weighted successor tap equations require
\[
 F_{\rm sil}(u)=2(\gamma-x)-\gamma k(u-2)=0 .
\]
With singleton ninth, \(F_9,F_{\rm sil}\) are coprime in the same good reduction. If ninth equals \(r\), \(F_{\rm sil}((x-r)/\gamma)\) is a unit. This establishes the exclusion without ever treating an invisible row as active.

Run `python3 check_tail.py` with `sympy==1.14.0` and `python-flint==0.9.0`. The replay uses exact \(\mathbb Q(\sqrt2)\) factors, followed by all their squarefree components at \(1009,t=285\). Every scalar divisor is a unit and the fixed-degree quadratic (or cubic for the silent test) supports lifting of the finite multiplication ranks. A hypothetical tableau need not itself admit reduction. The [native receipt](../../lean/RKCert/ReviewedNative/SDIRK8InvisibleGaussDoubleReceipt.lean) verifies the denominator-free reverse cross relation and the removable zero-gap identity. The chart reduction and finite arithmetic remain source-level proofs.

The [eight-distinct follow-up](../sdirk-eight-silent-two-distinct/README.md) now excludes the remaining eight-clock case. Together these results exclude exactly two individually invisible quadratic-defect stages at the same physical clock; the other visibility patterns remain outside this conclusion.
