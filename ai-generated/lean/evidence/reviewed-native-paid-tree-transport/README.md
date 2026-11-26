# Paid scalar transport for literal trees

[PaidTreeTransport](../../RKCert/ReviewedNative/PaidTreeTransport.lean)
compares the formal unit moments of layer-reduced and unreduced
polynomial columns on a paid height and order band. A graft's base
is an unfinished product at the same root and stays raw. Its actual
child is reduced before the shifted primitive acts. A completed root
may then be reduced once. The unreduced reference is the existing
literal `Model.column` with the checked shifted primitive as its action.

Over a field, the terminal theorem assumes `PaidUnits`, reducers
that do not increase degree and fix the constant one, and an explicit
`LocalCut` scalar receipt at each positive layer. A receipt compares a
weighted unit moment before and after one reduction within the two
paid degree bounds. At saturation the required test is the particular
pure unary test from the [paid shift adjoint](../reviewed-native-paid-shift-adjoint/README.md).
The [native height and grade](../common-diagonal-height/README.md)
control a single simultaneous raw/value induction. A saturated child
forces its same-root base to be a leaf, giving exactly the next pure
unary test. The result allows all local cuts at once and claims scalar
agreement, not polynomial-column equality. It does not provide the
local receipts or build a hull, interpolation row, physical tableau,
quadrature, or order or stage bound.

## Measured checks

The unchanged body passed with an empty log. The
[standalone typed audit](../../AuditPaidTreeTransport.lean) passed five
literal field-only clients with no generated object: raw recursion,
value and ideal model, grade bounds, the public weighted `LocalCut`
receipt on a literal raw tree, and the terminal band endpoint. The
weighted induction itself is private and is exercised through the
public terminal theorem. The [unmodified transcript](typed-audit-output.txt)
records seven named [stock-only axiom reports](actual-axioms.tsv).
Sources, actual and wrapper exits, and receipt hashes are recorded in
[acceptance.tsv](acceptance.tsv).

The only direct project providers are the checked `PaidShiftAdjoint`
and `CommonDiagonalHeight`, with one private stock Omega import.
Their [direct measured identities](direct-provider-identities.tsv)
and [16 exact project source hashes](reviewed-providers.sha256) are
recorded. The body used one coherent project root with 80 accepted
fragments. The audit kept all 80 and added the [five exact new body
fragments](transport-fragments.tsv) to one project root. The stock cut
was unchanged at 3,560 modules, 21,360 measured source and object
bindings, and the same 8,030 Mathlib projection links. No compiled
objects are included here.

These are warm serial measurements with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, not a cold build or a
separate leanchecker result. To replay with the pinned toolchain and
dependencies already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-tree-transport/added-sources.sha256
    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-tree-transport/reviewed-providers.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.PaidTreeTransport
    lake env lean -j1 -M3000 AuditPaidTreeTransport.lean
