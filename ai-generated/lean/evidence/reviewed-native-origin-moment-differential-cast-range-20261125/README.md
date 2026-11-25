# Origin-moment differential criterion with finite natural cast bounds

Import [RKCert.ReviewedNative.OriginMomentDifferentialCastRange](../../RKCert/ReviewedNative/OriginMomentDifferentialCastRange.lean).
This is an additive sibling of the checked [characteristic-zero module](../reviewed-native-origin-moment-differential-20261125/README.md),
whose statements and source are unchanged. It uses the same moment window
on a polynomial of degree at most n+2, with double origin and n paid
formal moments. The added proposition NatCastsThrough K D requires (k:K)
to be nonzero for every positive natural k at most D; no new typeclass
is imposed.

The degree-(n+1) kernel uses this condition through 2n+1. The differential
scalar and both complementary regular-root implications use it through
2n+2. Independently, the regular-ODE root criterion needs only
nonvanishing casts of the alleged multiple root's multiplicity and its
predecessor. These are generic algebraic statements over a field, not
a new RK order result, a prime-specific adapter, or a positive
characteristic threshold corollary stated in Lean.

## Measured stock checks

Stock Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The exact original body (41765) compiled with four lint warnings, two at
each measured tactic site. Its [portable diagnostic log](body-diagnostics.txt)
replaces only the original source path. The [standalone typed audit](../../AuditOriginMomentDifferentialCastRange.lean)
(17870) elaborated five literal Field-only clients and emitted no module
artifacts. Its [exact transcript](typed-audit-output.txt) gives six
named reports using only standard axioms, itemized in the
[axiom ledger](actual-axioms.tsv). The audit reused the five measured
body fragments and nine already accepted project modules in one coherent
projection, with the identical stock external family. See the
[acceptance ledger](acceptance.tsv), [generic providers](generic-providers.tsv)
and [fragment hashes](stock-fragments.tsv). No compiled objects or
local execution paths are included.

Integration base checked: b1cab93f6b2678990949871909ac7e795bb981c9.
No package configuration is changed. The evidence is a warm serial
body check plus a stock no-output audit, not a cold build or a separate
leanchecker run. To replay with the pinned toolchain and dependencies
already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-origin-moment-differential-cast-range-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.OriginMomentDifferentialCastRange
    lake env lean -j1 -M3000 AuditOriginMomentDifferentialCastRange.lean
