# Finite beta-moment support bound

The [Lean body](../../RKCert/ReviewedNative/BetaGapScalar.lean)
first eliminates the zeroth coefficient using the zero endpoint sum.
The remaining square test is the reviewed finite Cauchy kernel.
It then uses a polynomial vanishing on a finite indexed family to
show that the cleared beta moments through exponent 2r force at
least r + 1 indices.

The result is over a field. Its arithmetic hypothesis is that the
positive natural casts through d + 2r + 1 are nonzero, with d > 0.
Labels need not be distinct. This is a scalar implication; it
neither produces moments from a tableau nor supplies a residue-ring
or gap-counting application.

The body and [standalone no-output audit](../../AuditBetaGapScalar.lean)
both exited zero without warnings with Lean 4.36.0 and the Mathlib
pin in [acceptance.tsv](acceptance.tsv). The audit elaborated two
literal clients: the coefficient test at d = 1 and the indexed
support bound without label injectivity. The [raw typed output](typed-audit-output.txt)
contains two named checks and two [stock-only axiom reports](actual-axioms.tsv).
The [reviewed provider](reviewed-providers.sha256) is pinned by source
hash. No compiled objects are included, and no other Lean version
is asserted.
