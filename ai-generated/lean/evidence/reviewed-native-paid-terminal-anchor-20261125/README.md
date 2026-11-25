# Native paid terminal anchor

Import [RKCert.ReviewedNative.PaidTerminalAnchor](../../RKCert/ReviewedNative/PaidTerminalAnchor.lean).
The native namespace is RKResearch.Certified.Graded.PaidTerminalAnchor.
For an original coordinate represented by a degree-a node polynomial
plus a genuine grade-a defect, each scalar moment with k+a+1≤p is the
one-coordinate moment. In particular the primitive at 1 is the physical
weight times the profile scale. Its nonzero value follows from the live
weight and nonzero scale, without any support arithmetic.

Over a characteristic-zero field, if the tableau kills that coordinate
column, the whole evaluated primitive belongs to the next defect grade.
At a clock-one terminal it normalizes an actual defect vector to a true
terminal-zero residual in the same grade. The strict Fin last-stage
wrapper builds the profile from reviewed tree-space membership and
strictness; it does not assume an auxiliary polynomial or a fitted tag.
It consumes live weight, clock one and tree-space membership; it does
not prove those inputs for all tableaux. No Jacobi nonvanishing,
chronology, case-specific adapter, stage bound or stage table is added.

## Measured stock checks

Stock Lean 4.36.0 and locked Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The [body](../../RKCert/ReviewedNative/PaidTerminalAnchor.lean) in measurement
81147 exited zero with a blank log. The [typed audit](../../AuditPaidTerminalAnchor.lean)
in measurement 43869 used its exact accepted object bytes and the same
11 generic native provider modules. The audit elaborated three literal
typed clients (including live anchor, forward membership, normalization
and the strict wrapper) and emitted no module object. All five
[named axiom reports](typed-audit-output.txt) list only propext,
Classical.choice and Quot.sound.

The original 35049 audit stopped during import: the body-only root
shadowed the following provider root and the loader looked for
PolynomialStageSeparation in the wrong project tree. The successful
retry uses one coherent project projection of the same fragments.
Both the audit source and compiler arguments were byte-identical;
nothing was recompiled or changed in either source. The
[acceptance](acceptance.tsv) and [repair](measured-repair-chain.tsv)
ledgers preserve the raw hashes and distinguish this import stop from
a proof failure. The successful audit transcript is byte-unchanged.
The [fragment](stock-fragments.tsv) and [generic provider](generic-providers.tsv)
ledgers contain digests, not compiled objects or local paths.

Integration base checked: d703297556dc6779b15f066900aacf289304d78c.
No package configuration file is changed. This is measured warm serial
body and no-output audit evidence, not a claim of a cold package build
or separate leanchecker pass. For optional replay with the pinned tools
and dependencies already installed, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-terminal-anchor-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.PaidTerminalAnchor
    lake env lean -j1 -M3000 AuditPaidTerminalAnchor.lean
