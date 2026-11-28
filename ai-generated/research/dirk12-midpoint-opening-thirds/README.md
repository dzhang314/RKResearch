# Exact third live row from the degree-36 opening gate

Scoped continuation of the [shared-mode fit and second live row](../dirk12-midpoint-opening-second/README.md). Physical row numbers are zero-based. The native results cover the actual opening through physical row 7, not the full real order-twelve tableau.

The new primitive payment uses the normalized cubic donor labels \(1,x,y\). The two annihilating positive-degree polynomials are \(P(T)=T(T-1)(T-x)(T-y)\) and \(T P(T)\). For \(J_j(z)=\int_0^z T^j P(T)\,dT\), write \(I_0=J_0(1)\), \(I_1=J_1(1)\), \(I_2=J_2(1)-\epsilon\). The determinant \(I_0I_2-I_1^2\) is \(-D_bD_c/10800\), so it is nonzero on the actual root box. The scalar pair
\[
 J_0(y)=r_y I_0+k_y I_1,\qquad J_1(y)=r_y I_1+k_y I_2
\]
uses the same \(r_y\) and the propagated literal \(k_y=K(\nu,y)\) from the already fitted mode system. It does not set a separate freely chosen local mode.

The only new algebraic consistency gate in that payment is
\[
 360[I_0J_1(y)-I_1J_0(y)]Q_0(x)
 -D_c x^3(x-1)^3 Q_0(y)
 =\tfrac{21}{4}xy(x-y)(y-1)G_3(x,y).
\]
The left-to-right identity is a native polynomial normalization. The archived \(G_3\) (34 bivariate terms) is proved to vanish at the actual root by one packed integer polynomial quotient by \(Q_{36}\) after substituting the denominator-cleared exact polynomial for \(y(x)\). Its substituted degree is 180 and quotient degree 144. The quotient and the norm bound are proved by kernel reduction; the generator is not trusted and no finite-characteristic root or numerical residual is substituted for the real relation. This gate does not need the later \(f\)-cubic.

The three coefficients are the actual causal positive-degree cardinals of the normalized live-only operator. The first three positive monomial reads are direct guarded interpolation, and the two kernel payments yield the fourth and compensated fifth by the literal three-label recurrence. Native code installs those coefficients in the real physical row. Entering powers 1–4 have zero actual forward defect there; entering power 5 has the exact profile \(6(1/2)^6 k_y(\epsilon+5/11088)\), including the unpaid sixth ghost excess.

**Remaining scope:** 24 explicit low live primitive equations (physical rows 8–13, powers 1–4), reverse flags beyond the first adjoint, and grade-six bridge pairings. None is asserted. The full exact all-tree existence proof remain in the separate mathematical packet.

After the second-row packet, build `IntegerPolyBivarReplay`, `DIRK12MidpointOpeningG3Data`, `DIRK12MidpointOpeningThird`, `DIRK12MidpointOpeningThirdPhysical`, and run `AuditDIRK12MidpointOpeningThird.lean`. Tested against repository-matched Lean/Mathlib 4.36.0, standard logical axioms only. To regenerate the data use `generate-g3.py <projection-directory> <output-lean-path>` with python-flint; the projection directory is `../dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection/` relative to this research directory.
