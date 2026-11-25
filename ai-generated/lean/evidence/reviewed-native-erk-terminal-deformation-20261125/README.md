# Checked generic terminal-row deformation

The [native module](../../RKCert/ReviewedNative/ERKTerminalDeformation.lean)
works with the reviewed Runge–Kutta order predicate over a commutative
ring. Appending a terminal block with no internal dependencies preserves
the old elementary columns on the original stages. The terminal rows
are baseline donor rows plus a scalar multiple of one contrast on
those original stages.

The theorem terminal_hasOrder preserves every paid rooted-tree
condition when the actual donor row law, quiet contrast condition,
copy moments, and outgoing clock-moment cancellation are supplied.
A mixed-moment induction on the reviewed trees proves the exact
order budget without enumerating trees or introducing a polynomial
quotient. The theorem terminal_clockMass reads the actual aggregate of
weighted matrix-vector outputs at a given physical clock. It keeps
both the baseline term and the contrast term, also when different
output labels share a clock.

The [unchanged typed audit](../../AuditReviewedNativeERKTerminalDeformation.lean)
checks the literal RKResearch.HasOrder predicate with the explicit
block weight vector, and the expanded weighted matrix-vector sum over
a clock fibre. Its [raw output](typed-audit-output.txt) contains exactly
two reports, both with only propext, Classical.choice, and Quot.sound.

## Measurement and scope

The body and separate no-output typed audit exited zero with Lean
4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The measured body loaded seven previously measured project modules.
The audit used the same coherent family and the five exact fragments
of the new module. It requested no output object and left its project
inputs unchanged. The [portable acceptance record](acceptance.json)
records the actual exits, source and log digests, stock reports,
and artifact digests. It also records the initial unsuccessful
body attempt separately; none of that attempt's outputs were used.
No compiled binary is shipped. These measurements were not a cold
package build or a compiler-compatibility result.

The module is conditional on the stated row and moment hypotheses.
This release does not verify a rational donor-bank construction,
a positivity or stage-minimum claim, or a particular tableau.

With that same pinned toolchain and dependencies already present,
the sources and named reports can be checked from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-erk-terminal-deformation-20261125/checked-sources.sha256
    cd ai-generated/lean
    LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.ERKTerminalDeformation
    LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeERKTerminalDeformation.lean
