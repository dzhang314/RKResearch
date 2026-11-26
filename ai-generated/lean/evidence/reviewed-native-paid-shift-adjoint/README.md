# Paid adjoint of the shifted polynomial primitive

[PaidShiftAdjoint](../../RKCert/ReviewedNative/PaidShiftAdjoint.lean)
uses the formal unit moment `unitMoment` and primitive `primitive` from
[ProjectedMomentContext](../projected-moment-context/README.md).
For a field and a scalar `γ`, it defines two actual linear maps on
polynomials: the shifted primitive `J(F) = I(F) − γF` and its paid
adjoint `T(W) = C(unitMoment W) − I(W) − γW`, where `C` embeds a
scalar as a constant polynomial. With `PaidUnits K p`, one application
moves `J` to `T` under the weighted moment when `deg W + deg F + 1 < p`.
Iterating gives the corresponding identity at cost `d`, using the strict
bound `deg W + deg F + d < p`. In particular, a zero forward moment of
`J^[d] F` implies a zero moment of `T^[d] 1 * F` on that paid range.
The body also bounds the degree growth of both maps and their iterates.
No characteristic-zero instance, polynomial hull, literal-tree
recurrence, tableau, or order construction is asserted here.

## Measured checks

The exact body exited zero with an empty log. The
[standalone typed audit](../../AuditPaidShiftAdjoint.lean) also exited
zero, emitted no compiled artifact, and checked four literal field-only
clients: both linear map signs, paid one-step transport, paid iterated
transport, and pure unary cancellation. Its
[unmodified transcript](typed-audit-output.txt) records five named
[stock-only axiom reports](actual-axioms.tsv). Actual and wrapper exits,
source hashes and terminal receipts are in [acceptance.tsv](acceptance.tsv).

The direct reviewed import was the checked `ProjectedMomentContext`.
The [direct provider identities](direct-provider-identities.tsv) pin
its source and five object fragments alongside the two explicit public
stock imports and private Omega import. The exact [reviewed source
cut](reviewed-providers.sha256) has 14 modules and 70 object fragments.
The stock closure is unchanged: 3,560 modules, 21,360 bindings, and the
same 8,030 Mathlib projection links. The audit added the [five measured
body fragments](adjoint-fragments.tsv) to the same single project
provider root and used the same stock roots. Only source and portable
measurement evidence are included, not compiled objects.

These are warm serial measurements with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, not a cold build or a
separate leanchecker result. To replay with the pinned toolchain and
dependencies already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-shift-adjoint/added-sources.sha256
    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-shift-adjoint/reviewed-providers.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.PaidShiftAdjoint
    lake env lean -j1 -M3000 AuditPaidShiftAdjoint.lean
