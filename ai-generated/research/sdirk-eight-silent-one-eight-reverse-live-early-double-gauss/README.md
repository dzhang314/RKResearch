# A literal quartic Legendre contact cannot be repeated at actual fourth

Use the [constant reverse-live nine-site chart](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) over characteristic zero. Its actual normalized cubic-defect profile on all nine sites is \(H(X)=(\alpha+\beta X)L_4(X)+\eta L_3(X)\), with no use of unpaid scalar precision beyond seven. Suppose the actual early literal clock \(a=\gamma A\), \(A=A_0\) or \(B_0\), is a root of \(L_4\). Then the actual fourth \(q=\gamma s\) **cannot** also be a root of \(L_4\). This statement does not require either clock to carry an ordinary weight, and does not exclude a single literal root. The unrestricted **10–11** interval stays unchanged.

If \(a,q\) are both quartic zeros their actual amplitudes \(H_a,H_4(s)\) read the same cubic coefficient, so
\[
 H_4(q/\gamma)L_3(a)-H_a L_3(q)=0.
\]
Both clocks are among the nine distinct reverse sites, including the genuinely reverse-live ordinarily silent stage; \(q\ne a\) is an actual, not merely aggregated, guard. Let \(r=a\) be a root of monic \(L_4/70\). Then \(\gamma=r/A\), and \(q\) is a root of the monic quotient \((L_4(X)/70)/(X-r)\) in the \(r\) algebra. The quartic and cubic are retained in full, so the proof models all distinct characteristic-zero root pairs. The two literal coefficient phases are in \(\mathbb Q(t)\), \(2t^2=1\), with \(A\ne0\).

At \((1129,t=203)\) the quartic has four simple roots \(100,214,916,1030\). The monic cubic at each root retains the other three simple roots, and the sharp guard \(q\ne r\) was implemented in the **exact** characteristic-zero model. The cleared comparison is a unit at all twelve full residue pairs for each early phase and chosen literal. This lifts through the finite monic bases and excludes all four orientations, without treating a modular collision as a true clock equality. The remaining early-Gauss chart has exactly one quartic contact among the three actual early stages and a nonzero fourth quartic value.

Install sympy==1.14.0 and python-flint==0.9.0, then run **python3 check_early_double_gauss.py** with the listed sibling utility folders. The [native comparison](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveEarlyDoubleGauss.lean) checks its cleared identity on Lean/Mathlib 4.36.0; the saturated profile and finite arithmetic are source-level.
