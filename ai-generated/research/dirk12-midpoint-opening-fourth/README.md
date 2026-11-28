# Exact fourth live row and its zero diagonal

This is a scoped native continuation of the [third live row](../dirk12-midpoint-opening-thirds/README.md). It proves the actual zero-based physical row 8 and does not by itself prove order twelve for the completed real tableau.

In normalized clock coordinates, the fourth live clock is \(t=t(x)\), represented by its exact degree-35 rational polynomial in the isolated \(Q_{36}\) root. Directed rational bounds prove \(0<x<t<y<1\), so all four original positive-degree cardinal denominators are nonzero. The new native equalities verify
\[
 J_0(t)=R(t)I_0+K(t)I_1,\qquad
 J_1(t)=R(t)I_1+K(t)I_2,
\]
where \(P(T)=T(T-1)(T-x)(T-y)\), \(J_j(s)=\int_0^s T^jP(T)\,dT\), \(I_0=J_0(1)\), \(I_1=J_1(1)\), and \(I_2=J_2(1)-\epsilon\). Both \(R(t)\) and \(K(t)\) come from the original shared mode fit, not independent local choices.

## What was packed

The first identity uses the proven affine relation for \((R+C_0)/Q_0\) and the already paid \(y\)-read. This removes \(D_c\) from its cleared numerator. The second is checked as the cross identity
\[
 I_0J_1(t)-I_1J_0(t)=(I_0I_2-I_1^2)K(t).
\]
It eliminates \(R(t)\) and uses the known factorization of the true local determinant. \(I_0>0\) is independently guarded by a small directed box. Direct polynomial normalization verifies the exact factors of the two cleared integer gates. Rather than pack all expanded monomials, the proof substitutes the exact polynomial expressions for \(y(x),t(x)\) into the reduced trivariate factors:

- Gate 0: 100 terms, degrees \((4,4,3)\), substituted degree 249, quotient by \(Q_{36}\) of degree 213.
- Gate 1: 59 terms, degrees \((5,2,3)\), substituted degree 179, quotient of degree 143.

The respective integer norm bounds fit in 3671 and 2614 bits. Kernel computation verifies both packed quotient identities and the norm bounds. Real-root evaluation follows from the exact \(Q_{36}\) equation and the independently audited denominator-cleared substitutions. No residue witness, floating-point equality, or unverified quotient is used.

## Actual row and scope

The two paid kernel identities make the three positive-clock donors \(1,x,y\) sufficient for all five entering degrees. Lean compares every one of the **four** original cardinal coefficients to the three-donor decode plus its literal zero at \(t\); the physical zero diagonal is therefore the original coefficient, not a projection or a modification of the method. The origin fill and actual ghost taps follow the already checked causal assembly. The actual scaled forward defects vanish for entering powers 1–4. Entering power 5 instead gives the exact profile
\(6(1/2)^6 K(t)(\epsilon+5/11088)\), retaining the unpaid sixth ghost moment.

The remaining low forward budget has 20 entries, the four entering powers at physical rows 9–13. This packet does not assert any unpaid reverse flag or the final grade-six bridge. The actual mathematical order-twelve witness remains documented separately.

After the third-row packet, build `IntegerPolyTrivarReplay`, `DIRK12MidpointOpeningTGate0`, `DIRK12MidpointOpeningTGate1`, `DIRK12MidpointOpeningFourthGates`, and `DIRK12MidpointOpeningFourthPhysical`; then run `AuditDIRK12MidpointOpeningFourth.lean`. All were verified with repository-matched Lean/Mathlib 4.36.0, using only the standard logical axioms. Rebuild the two generated files with `generate-t-gates.py <original-field.json> <output-dir>` using python-flint and SymPy. The original field is the `field.json` in `../dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection/`. The generated source was checked byte-for-byte on replay.
