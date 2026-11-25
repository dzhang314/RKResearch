# Checked paid positivity obstruction

The [native module](../../RKCert/ReviewedNative/PaidPositiveDefectObstruction.lean)
uses the reviewed Runge–Kutta order predicate over an ordered field.
It works with actual graded defects and the actual tableau matrix.
The conclusions are pointwise on physical stages or donor links, not
just cancellation after grouping stages by time.

- At order budget \(g+g+1\le p\), nonnegative weights and the paid
  square of a grade-\(g\) defect \(v\) force \(b_i v_i=0\) at every stage.
- At \(g+g+2\le p\), if every effective link \(b_i A_{ij}\) is
  nonnegative, the paid action on \(q^2\) forces every
  \((b_i A_{ij})q_j=0\) and every \(b_i(Aq)_i=0\). There is no
  separate sign assumption on the weights in this statement.
- At \(g+g+3\le p\), nonnegative weights alone force \(b_i(Aq)_i=0\)
  by paying the square of the outgoing column.

The [unchanged typed audit](../../AuditReviewedNativePaidPositiveDefectObstruction.lean)
checks those three literal conclusions and the reviewed order predicate.
The [raw audit output](typed-audit-output.txt) contains exactly the
three corresponding reports, with only propext, Classical.choice,
and Quot.sound.

## Measurement and scope

The exact body and the separate no-output audit both exited zero with
Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body used seven already measured project providers. The audit
reused their exact fragments and those of the new body in a single
project root, and left its inputs unchanged. The
[portable acceptance record](acceptance.json) binds the measured source,
output and report digests. No compiled object is shipped, and the
measurements are not a cold-build or compiler-compatibility result.

The sign and paid-order conditions are explicit hypotheses. There is
no positivity search, SSP claim, stage bound, or tableau construction.

With pinned dependencies already available, the sources and named
reports can be checked from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-positive-defect-obstruction-20261125/checked-sources.sha256
    cd ai-generated/lean
    LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.PaidPositiveDefectObstruction
    LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativePaidPositiveDefectObstruction.lean
