# Exact shared-mode fit and physical second live row of the DIRK12 midpoint method

Scoped native continuation of the [real forward wiring](../dirk12-midpoint-real-forward-native/README.md). This verifies the original Legendre-mode coefficient selection and all four low primitive equations at zero-based physical row 6. It does **not** claim a native proof of the completed real tableau's order 12.

Write \(T=X/a\) with \(a=1/2\), and let \(x\) and \(y\) be the second and third normalized live clocks from the exact midpoint field. For the fixed shifted Legendre derivatives, define
\[
 Q_0(T)=T L_6'(T/2),\qquad
 P_0(T)=T[L_5'(T/2)+(6/7)L_7'(T/2)].
\]
The first clock still fixes \(\gamma=(30\alpha-8)/35\). The exact identity
\(P_0(T)=(13/7)(T-1)Q_0(T)\) reduces the remaining two equation rows to an affine difference. Their determinant is
\((13/7)(x-y)Q_0(x)Q_0(y)\). Directed rational guards on the original \(x,y\) boxes give \(0<x<y<1\) and \(Q_0(x),Q_0(y)<0\). They also give \(D_b=5x^2-5x+1>0\), \(D_c=2xy-x-3y^2+2y<0\). Lean defines the unique shared fitted \(\alpha,\mu,\nu\), verifying the normalized \(R\) probes at \(1,x,y\) and the \(K\) probe at \(x\). These are the exact four equations in the original mode selection, not a refit against approximate clocks.

The second live row has two non-ghost coefficients before the origin fill:
\[
 A_{6,5}=a\ell_0,\qquad A_{6,6}=a\ell_1,\qquad
 \ell_0=\frac{x^3(x-1)(5x^2-6x+2)}{2D_b},\qquad
 \ell_1=\frac{x(x-1)(2x-1)}{2D_b}.
\]
The explicit expressions are checked to equal the existing positive-degree cardinal solution. For entering monomial \(T^m\), the normalized live read equals
\[
 \ell_0+\ell_1x^m
 =\frac{x^{m+1}-r_x}{m+1}-\frac{k_x}{m+2}
   +\mathbf 1_{m=5}k_x\epsilon,\qquad 1\le m\le5 .
\]
The four physical ghost feeds are the same taps as before; the physical scaled forward defect vanishes for \(1\le m\le4\). At entering power 5 the exact physical defect is instead
\(6(1/2)^6 k_x(\epsilon+\Delta)\), where
\(\Delta=\sum_g\ell_g p_g^6-1/7=5/11088\) is the actual unpaid sixth ghost-tap moment. A portable arithmetic lemma also records
\(\sum_g\ell_g h_g p_g^3=-1/47520\) for grade-six action on the third generator. No unpaid moment is treated as exact.

The two literal first-live rows are now kernel-certified. `OpeningRemainder` contains 28 remaining forward primitive tests, the four entering powers at physical rows 7 through 13. The reverse flags beyond the first adjoint and the single grade-six bridge are not discharged. The new reusable single-row read relates the physical forward equation to its deghosted budget without assuming any other row.

Build after the scoped real-forward packet, in order `DIRKOrderTwelveMidpointOpeningGhostCore`, `DIRK12MidpointOpeningModes`, `DIRK12MidpointOpeningRead`, `DIRK12MidpointOpeningSecond`, then run `AuditDIRK12MidpointOpeningSecond.lean`. The portable ghost check passed Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The Mathlib-dependent mode and physical certificates and typed audit passed the repository-matched Lean/Mathlib 4.36. Their reported axioms are the standard logical axioms only; no `native_decide` or `sorry` is used.
