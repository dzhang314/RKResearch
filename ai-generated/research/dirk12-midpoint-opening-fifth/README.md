# Fifth live row of the real midpoint DIRK12 construction

This scoped native packet installs zero-based physical row 9 of the existing fifteen-stage construction. It continues the [fourth live row](../dirk12-midpoint-opening-fourth/README.md). It does not assert the still-unverified reverse realization or full real order twelve in Lean.

The five normalized available live clocks are exactly \(1,x,y(x),t(x),2f\), in physical chronology. Native Lean obtains their distinctness and nonzero values from the already checked cardinal support of the real tableau. The exact denominator of each positive-degree cardinal is its own clock times the product of differences from the other four; all these denominators are guarded. Using Mathlib's interpolation theorem, the native cardinal maps reconstruct the five monomials \(T,\ldots,T^5\), not the constant. This is the entire degree budget of the original live-only opening operator, so this row needs **no additional \(Q_{36}\) relation**.

For its five literal live coefficients, take the original positive-degree cardinal polynomial
\[
 \ell_i(T)=\frac{T}{s_i}\prod_{j\ne i}\frac{T-s_j}{s_i-s_j}
\]
and apply the prescribed normalized linear read, whose monomial values are
\[
 F_m=\frac{(2f)^{m+1}-R(2f)}{m+1}
      -\frac{K(2f)}{m+2}+\mathbf 1_{m=5}K(2f)\epsilon .
\]
The new native helper verifies the exact nodal-product formula for these cardinals, the nonzero denominators, and recovery of all five reads. It then installs all five coefficients in the physical matrix after multiplying by \(a=1/2\). The modes are exactly the previously fitted shared functions \(R,K\) evaluated at \(2f\), with no new local choice.

Lean certifies the actual four paid primitive defects on row 9 are zero. The entering-power-five defect is
\(6(1/2)^6 K(2f)(\epsilon+5/11088)\), preserving the unpaid sixth ghost excess. The fixed four earlier opening rows keep their previous proofs. The remaining low forward budget is now **16 tests**, for the four positive entering powers at zero-based rows 10–13. Their intended payment is via the independent [late three-clock adapter](../dirk12-midpoint-late-completion/README.md), after the grouped reverse conditions are established. No grouped condition is assumed proved here.

After the fourth-row packet, build `PositiveCardinalRead` and `DIRK12MidpointOpeningFifth`, then run `AuditDIRK12MidpointOpeningFifth.lean`. All were checked with repository-matched Lean/Mathlib 4.36.0 and standard logical axioms only. The packet contains no new large generated data.
