# Centered grade payment for the paired origin residue

Import `RKCert.ReviewedNative.DIRKPairedOriginGradeBridge`. This is a
bridge from the two previously checked original-tableau residuals to
the actual graded zero spaces. The cleared residuals have grades 3
and 4 over an arbitrary field. Expressing them with the normalized
`mDef` needs respectively `3 ≠ 0` and `2 ≠ 0, 3 ≠ 0` in the field.
Normalization is not used to prove the cleared grade memberships.

The centered grade is `zeroSpace A j` restricted to columns that
vanish at physical row zero. If the first row has only the diagonal
`γ`, the column `originResidual A γ + lam • nextResidual A γ` has
centered grade 4 for any caller-supplied `lam`. Multiplication by a
clock polynomial of degree at most `d` adds `d` to the grade without
any unit assumptions. The actual `A` action adds one grade and
preserves the origin kernel when the displayed tree-order casts are
units. If the recipient annihilates the resulting centered grade
`4 + d + 1`, all the displayed degree-at-most-`d` weighted probes
vanish there. That annihilation is a separate hypothesis, not a
consequence of order claimed here. This does not choose a scalar
that realizes a joint mask, establish rank or band saturation, or
prove an order-specific case or stage bound.

## Exact measured check

The [body](../../RKCert/ReviewedNative/DIRKPairedOriginGradeBridge.lean)
and [unchanged standalone typed audit](../../AuditReviewedNativeDIRKPairedOriginGradeBridge.lean)
both exited zero with Lean v4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The body had four ordinary
sequencing linter warnings and no errors; the repair preceding this
check renamed one reserved binder and its six other bound occurrences,
without changing any formula or imports. The six typed examples check
the two normalized formulas, centered grade 4, clock multiplication,
the unit-charged matrix lift, and conditional payment at a recipient.
The audit emitted no object and its [unchanged output](typed-audit-output.txt)
reports exactly `propext`, `Classical.choice` and `Quot.sound` for
all six named declarations.

[Acceptance](acceptance.tsv) records the exact source, exit and raw
log hashes. The body primary is an observed build hash, not a shipped
binary. All 14 project dependencies, including the prior raw paired
residue, matched their measured sources at base
`5642ebb61b116ae83ac1d59a6e48d820fd68b2ba`. The checks used one serial
resolver with 3,393 pinned external modules. Neither a cold build
nor compatibility with another toolchain pair was measured.

To replay the source check from the repository root, with the pinned
toolchain and dependencies already available:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-dirk-paired-origin-grade-20261125/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.DIRKPairedOriginGradeBridge
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeDIRKPairedOriginGradeBridge.lean
```
