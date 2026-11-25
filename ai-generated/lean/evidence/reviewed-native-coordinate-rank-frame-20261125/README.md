# Practical coordinate restrictions at exact rank

Import [RKCert.ReviewedNative.CoordinateRankFrame](../../RKCert/ReviewedNative/CoordinateRankFrame.lean).
For a subspace of columns on a finite original stage type over a field,
the module selects exactly its dimension many distinct ambient labels
so that evaluation on them is injective. Equal dimensions then give an
equivalence with functions on those labels. There is no assumed pivot,
nonempty-stage requirement, or characteristic hypothesis.

The transpose of the ordinary coordinate restriction extends a selected
row to the real ambient coordinates, with the original coefficients on
the chosen labels and zero elsewhere. The inverse frame's transpose
treats any subspace functional as a row on the selected coordinates.
Combining these two maps gives a genuinely supported ambient extension
of that functional, with exact agreement on the given subspace.
No unrolled tableau, height or order recursion, diagonal, quadrature,
or minimum-stage assertion enters this module.

## Measured stock checks

Stock Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The exact original body (96433) compiled with one letI style warning
at line 55. The [portable diagnostic log](body-diagnostics.txt) changes
only the source path and trailing whitespace. The [standalone typed audit](../../AuditCoordinateRankFrame.lean)
(33335) elaborated five literal generic clients without producing a
module artifact. Its [exact stock transcript](typed-audit-output.txt)
gives eight named reports, all using only the three standard axioms;
see [axiom ledger](actual-axioms.tsv). It reused the five measured frame
fragments and six measured project prerequisites in one coherent
provider root, with the same stock external family. See the
[acceptance ledger](acceptance.tsv), [generic providers](generic-providers.tsv),
and [frame fragment hashes](stock-fragments.tsv).

Integration base checked: 127c66265145f035979f902bf01aa0a36dfa3ec2.
No package configuration, compiled object or local execution path is
included. This is warm serial body and typed no-output evidence, not a
cold build or a separate leanchecker run. To replay with the pinned
toolchain and dependencies already available, from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-coordinate-rank-frame-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.CoordinateRankFrame
    lake env lean -j1 -M3000 AuditCoordinateRankFrame.lean
