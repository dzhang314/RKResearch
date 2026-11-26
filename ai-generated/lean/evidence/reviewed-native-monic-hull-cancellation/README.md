# Monic-hull scalar cancellation

Import [RKCert.ReviewedNative.MonicHullCancellation](../../RKCert/ReviewedNative/MonicHullCancellation.lean).
Over a field, reducing a polynomial modulo a monic hull leaves it
unchanged below the hull degree. At or below that degree the
discarded polynomial is the hull times a scalar, read from the
monic quotient. A linear map into any module therefore ignores
the discarded term when it annihilates the hull. The body gives
symbolic clients for zero error below the degree and a nonzero
leading-coefficient scalar at saturation. It uses only stock
polynomial division and linearity, with no characteristic-zero,
root or interpolation hypothesis. There is no tree, paid-adjoint,
recurrence or numerical-order statement.

## Measured stock checks

The original body passed with an empty diagnostic log. The
[standalone typed audit](../../AuditMonicHullCancellation.lean)
passed three literal clients with no generated artifact. Its
[unchanged transcript](typed-audit-output.txt) records three named
stock-only axiom reports, summarized by [actual-axioms.tsv](actual-axioms.tsv).
Both actual and wrapper exits are recorded in [acceptance.tsv](acceptance.tsv).

The toolchain was stock Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body's only direct import was Mathlib.Algebra.Polynomial.Div,
with [six measured source and object identities](stock-provider.tsv).
The exact measured stock subset contains 2,989 keys and 17,934
identities; it was reused from the checked polynomial division
family. The body used no project ancestor. The audit reused the
same stock subset plus the [five exact body fragments](stock-fragments.tsv)
in one project root. This package contains source and portable
evidence only, not those compiled artifacts.

Integration base checked: 3fac4d3540e44aad549a20841c879fd46b1a7463. These are warm
serial body and no-output measurements, not a cold build or
a separate leanchecker result. To replay with the pinned
toolchain and dependencies already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-monic-hull-cancellation/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.MonicHullCancellation
    lake env lean -j1 -M3000 AuditMonicHullCancellation.lean
