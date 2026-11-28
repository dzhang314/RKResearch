# Portable nine-label and ten-distinct scalar gates

The core-only module
[ERK10NineLabelHeadScalars.lean](../../lean/RKCert/ReviewedNative/ERK10NineLabelHeadScalars.lean)
checks the full denominator-cleared **reduced \(2\times2\)**
compatibility numerator, both affine anchor evaluations after
the exceptional repeat, and the \(\kappa=1/2\) next-row exit.
It imports no Mathlib. Lean 4.34.1, 4.35.0, 4.36.0, and
4.37.0-rc1 all passed with standard axioms only.

To connect the reduced numerator to the \(5\times5\) matrix
in the proof, eliminate the first two old taps with the first
two rows and then eliminate the target score with its first
scalar moment. The independent [exact row reduction](audit_reduced.py)
reconstructs the four resulting entries before clearing the
displayed common factors. The separate [full arithmetic replay](audit.py)
computes the original \(5\times5\) determinant, repeated-row
minors, and guarded post-closure \(5\times5\) Cramer ratio.
Thus the original matrix is checked exactly in Python/Sympy,
not as an unreduced Lean determinant. The proof of the word,
rank and chronology implications is mathematical.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10NineLabelHeadScalars.lean
    python3 -B ai-generated/research/erk10-five-opening-nine-label-one-pair/audit_reduced.py
    sha256sum -c ai-generated/research/erk10-five-opening-nine-label-one-pair/lean-checked.sha256
