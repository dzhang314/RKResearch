# Finite height/order band unrolling

Import [RKCert.ReviewedNative.FiniteBandUnroll](../../RKCert/ReviewedNative/FiniteBandUnroll.lean).
For a dense reference matrix over a field on a finite stage type, each
new layer uses a coordinate frame for the span of reference tree
columns of height at most its layer index and order at most that index
plus a fixed lead. The matrix sends only from the preceding layer and
the weights are supported on the terminal layer. A frame is available
without a supplied pivot or rank hypothesis.

For the resulting matrix and weights, the scalar output agrees with the
reference for every tree of height at most the terminal index and order
at most that index plus the lead. Every higher tree has zero output,
without an order restriction. These statements do not assume the
reference is causal, and make no claim about its own higher outputs.
They do not assert RK order, a diagonal-shift or quadrature construction,
or stage minimality.

## Measured stock checks

The exact body (76205) passed with an empty diagnostic log. The exact
[standalone typed audit](../../AuditFiniteBandUnroll.lean) (55367)
checked the band agreement with arbitrary supplied frames and the
higher-tree zero with the unconditional frame choice. It emitted no
module artifact. Both named axiom reports are stock-only; see the
[exact transcript](typed-audit-output.txt) and [axiom ledger](actual-axioms.tsv).

Both used stock Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body used twelve measured project providers in one root. The
audit used the same providers and the five exact body fragments in
one root, with the same external stock closure. The [acceptance ledger](acceptance.tsv),
[provider source and primary-object hashes](generic-providers.tsv), and
[body fragment hashes](stock-fragments.tsv) record the measurement.
Integration base checked: b31f9188a998b760d736b2c81abdfe39cfeb9178. No package configuration,
compiled object, or machine path is included. This is warm serial
body and no-output audit evidence, not a cold build or separate
leanchecker result.

With the pinned toolchain and dependencies already available, replay
from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-finite-band-unroll-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.FiniteBandUnroll
    lake env lean -j1 -M3000 AuditFiniteBandUnroll.lean
