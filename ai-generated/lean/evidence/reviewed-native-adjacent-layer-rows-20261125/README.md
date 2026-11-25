# Adjacent-layer row and literal graft step

Import [RKCert.ReviewedNative.AdjacentLayerRows](../../RKCert/ReviewedNative/AdjacentLayerRows.lean).
On a finite stage type indexed by layer and its fibre, the adjacent
mask keeps only entries from the immediately preceding layer.
A receiving matrix row then evaluates as the ordinary dot product
on that parent fibre, so an explicitly paid action on a matching
parent column transfers to the actual masked matrix. The first
layer acts by zero, and an output row supported on one fibre can
be evaluated using that fibre alone.

The native graft lemma transports one literal graft from its base
value and the supplied parent-row payment. These are generic local
statements over a commutative semiring. No coordinate-rank frame,
whole-tree induction, global layer assembly, diagonal, or order
assertion is used or concluded.

## Measured stock checks

Stock Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The original body (92347) passed with four warnings: two deprecated
conditional-lemma names and two unused section-instance warnings.
The [portable diagnostic log](body-diagnostics.txt) changes only
the original source path prefixes. The [standalone typed audit](../../AuditAdjacentLayerRows.lean)
(69331) elaborated five literal clients and emitted no module artifact.
Its [exact transcript](typed-audit-output.txt) records seven named
reports using only standard axioms; see [axiom ledger](actual-axioms.tsv).
The audit reused the five body fragments alongside the two measured
project ancestors in one coherent project root, with an unchanged
stock external path. See [acceptance ledger](acceptance.tsv),
[generic providers](generic-providers.tsv), and
[body fragment hashes](stock-fragments.tsv).

Integration base checked: d5b76782cbe8399e13b3447761ca31aaf721c535.
No package configuration, compiled object or local execution path is
included. This is warm serial body and typed no-output evidence, not a
cold build or a separate leanchecker run. To replay with the pinned
toolchain and dependencies already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-adjacent-layer-rows-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.AdjacentLayerRows
    lake env lean -j1 -M3000 AuditAdjacentLayerRows.lean
