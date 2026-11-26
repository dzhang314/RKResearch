# Checked additive next-tall correction on the native RK trees

The common-diagonal adjacent path gives a concrete output direction that
reads zero against every actual native tree column through order p = n+1
and reads one against the literal next tall tree. These are raw Φ column
reads over a commutative ring, not normalization by a tree factorial.

The transfer theorem is conditional. For an existing matrix A with order p
and an output direction d with those two raw read properties on this same A,
replace b by b − (b · Φ_next(A)) d. The matrix is unchanged. Over a
nontrivial commutative ring, the replacement preserves native HasOrder p
and violates HasOrder (p+1); it kills the raw next tall read without
requiring an inverse of (p+1)!. This is not an existence theorem for the
underlying tableau, an interpolation formalization, or a stage-count
certificate.

The [measured body](../../RKCert/ReviewedNative/PathExactnessCorrection.lean)
and its [standalone typed audit](../../AuditReviewedNativePathExactness.lean)
both exited zero under the recorded stock Lean 4.36.0 dependency cut. The
body retains its seven unused-simp-argument warnings. The audit requested
no object output and checks the paid-zero, next-tall-one, and literal
same-tableau HasOrder transfer statements. Its
[exact transcript](typed-audit-output.txt) reports only the standard
axioms propext, Classical.choice, and Quot.sound for these three names.
The [result ledger](result.json) records the source, object and actual
diagnostic hashes. The two pre-existing native providers are unchanged.

Integration base checked: 3fac4d3540e44aad549a20841c879fd46b1a7463.
This is an additive sources-only evidence publication. It includes no
compiled objects, package configuration changes, or cold-build claim.
