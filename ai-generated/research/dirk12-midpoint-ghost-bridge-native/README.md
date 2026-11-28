# Paid grade-six Legendre bridge and literal ghost images

This scoped native companion to the [paid scalar probes](../dirk12-midpoint-paid-probes/README.md) establishes the **actual** \(AG_5\) bridge conditional only on the stated reverse-band properties. It does not assert that the still-open reverse realization satisfies those properties.

For any vector \(\mathbf w\) with ordinary nonterminal live profile \(\rho\,\mathbf c L_6'(\mathbf c)\), arbitrary ghost values, and zero actual output, the native bridge checks annihilation of both \(\mathbf W(P_5)\) and \(R_5\) from the following exact conditions:

- all ghost output weights vanish and the literal terminal has \(c=1\);
- every test vector in \(R_5\) is zero on the ghosts and literal terminal and annihilates scalar powers through degree six;
- the actual reflected quadrature is paid through degree eleven.

For positive reflected probe degree, the terminal disappears; the degree-six Legendre profile has the five paid tests from the scalar packet. The zeroth probe is precisely the given actual output. The \(R_5\) test only sees the ordinary nonterminal polynomial profile through degree six, so it vanishes. No terminal value is guessed and no extra moment is used.

This applies unconditionally to the literal ghost image profile: with four ghost rows in the forward construction, the grade-five space is spanned by the three supported columns \(\mathbf h,\mathbf p\mathbf h,\mathbf p^2\mathbf h\). The first two have zero \(A\) image on ordinary nonterminal rows. For the third, the literal rational moment \(\sum_g\ell_g h_g p_g^3=-1/47520\) gives the exact coefficient \(-a\nu/47520\) multiplying \(c_i L_6'(c_i)\). The actual weighted output of every ghost generator image is zero by the previously verified first adjoint. Thus the reviewed `bridge_A` conclusion is verified for the actual physical assembly, with only the three stated \(R_5\) properties still supplied as hypotheses. No grouped live-to-live entries are used in this proof.

The bridge for the **true quintic primitive** can use the same theorem after its remaining late-row profile is established. This separate file does not assert that last realization. Build `DIRK12MidpointPaidBridgeProfiles`, then `DIRK12MidpointGhostImageBridge`, and run `AuditDIRK12MidpointGhostBridge.lean` after the paid scalar-probe packet. Tests used the repository-matched Lean/Mathlib 4.36.0 and standard logical axioms only.
