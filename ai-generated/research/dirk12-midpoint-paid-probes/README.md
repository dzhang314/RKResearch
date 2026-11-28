# Paid scalar targets for the late three-clock test

This packet verifies scalar targets and their true weighted physical probes, **not** the grouped reverse realization. It may be combined with the [late three-clock adapter](../dirk12-midpoint-late-completion/README.md) once the actual reverse pair transfer and relevant primitives are known. It does not claim full order twelve in Lean.

For \(d=5,6,7\), let the reflected polynomial be \(B_d(Y)=(1-Y)L_d'(1-Y)\), where \(L_d\) is the shifted Legendre polynomial. The exact rational kernel core verifies
\[
       \int_0^1 Y^k B_d(Y)\,dY = \mathbf1_{k=0}\qquad (0\le k<d).
\]
The native proof verifies the actual polynomial evaluation \(B_d(1-c_i)=c_i L_d'(c_i)\), the degree bound, and the weighted physical identity when additionally \(k+d\le11\). In particular, the degree-six profile has unit output and its first five positive reflected probes vanish. Arbitrary linear combinations of the three mode shapes also have the four paid positive reflected probes \(k=1,\dots,4\) equal to zero. The proof does **not** use the unproved degree-twelve moment.

The monic reflected opening hull \(Q^\#(Y)\) is the degree-six nodal polynomial through the reflected origin and all five opening live clocks. Its product with \(Y\) is the already checked fixed hull \(P_*(Y)\); write \(n_j=\int_0^1Y^jP_*(Y)\,dY\). The actual degree-six nodal forward profile candidate, before adding the (separately paid) Legendre ghost mode, is
\[
 W(Y)=\Lambda(u-Y)Q^\#(Y)-\int_Y^1 Q^\#(s)\,ds,\qquad
 \Lambda=\frac{3n_1^2-2n_0n_2}{6(n_0n_2-n_1^2)}.
\]
The moving denominator is strictly positive by the same directed real moment bounds. The new generic polynomial operator evaluates the primitive from \(Y\) to 1 and proves the exact polynomial integration-by-parts identity. Thus the \(k\)-th positive reflected integral of \(W\) is
\[
       \Lambda(u\,n_{k-1}-n_k)-\frac{n_k}{k+1}=0,\qquad k=1,2,3.
\]
These are the already verified moment relations in their actual indexed and guarded form: the first two are polynomial identities; the third uses the verified \(Q_{36}\)/\(f\)-cubic relation. The degree of \(W\) is at most seven, so every probe spends at most degree ten. Native Lean transfers these to the actual physical weight row without forming any degree-eight interpolant.

The core table passed Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The polynomial and actual physical results and typed audit passed the repository-matched Lean/Mathlib 4.36.0. Build `DIRK12MidpointLegendreProbeCore`, `DIRK12MidpointLegendreProbes`, `DIRK12MidpointPolynomialPrimitive`, `DIRK12MidpointPaidNodalProbes`, then run `AuditDIRK12MidpointPaidProbes.lean`. Standard logical axioms only.
