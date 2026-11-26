# Finite indexed moments in a maximal residue field

The [Lean body](../../RKCert/ReviewedNative/IndexedResidueMoments.lean)
maps the cleared scalar equations without changing the finite index type
or the exponent range. A factorial normalization becomes the exact target
factorial cast. A top factorial is a unit precisely when the positive
natural casts through that bound are all units.

Over a nontrivial commutative ring, one can choose a maximal ideal and
specialize the equations into its residue field on the original indices.
All factorial units through the bound survive, and all positive natural
casts through the bound are nonzero in the field. The quotient need not
preserve distinct values or nonzero weights. There is no support
regrouping, tableau, or stage-count claim.

The body and [standalone no-output audit](../../AuditIndexedResidueMoments.lean)
exited zero with Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The body uses only two explicit stock
imports and no project provider. Two nonfatal style warnings in the
unchanged body are identified in the [warning admission](body-warning-admission.tsv).
The audit elaborated three literal clients without warnings. Its
[unmodified output](typed-audit-output.txt) has five named checks and
five [stock-only axiom reports](actual-axioms.tsv). No compiled objects
are included, and no other Lean version is asserted.
