# Native algebra and rooted bridge for the literal SDIRK(14,9) packet

The module verifies the actual single-tap determinant and two-tap solve, the
raw-to-mean weighted conjugation, the order-nine specialization of the
reviewed single-defect rooted bridge, and both chronological diagonal-twin
contractions into 14 actual stages. The rooted theorem is conditional on
literal seed, shorter-word and longest-word payments, which the accompanying
mathematical construction proves for the specific algebraic tableau.

The 312-bit dyadic root fixture and proof by directed rational contraction
are replayed separately in Python. Thus this module is **not** an
unconditional Lean existence theorem for those constants. This packet
does not assert a new smaller upper endpoint.

Tested on Lean 4.36.0 with the reviewed checkout's pinned Mathlib objects
and the human-authored RKResearch elementary tree modules. No native
decision axiom is used. The typed signatures and exact axiom reports are
in audit-4.36.0.log. The new module elaborates without diagnostics.

Build the existing reviewed modules in their ordinary library graph:
GradedColumns, MergeEqualRows, DiagonalTwin, PaidDefectBridge, then the
new RKCert.ReviewedNative.SDIRK149CausalMixed. With its output and the
reviewed dependencies on LEAN_PATH, run lean on Audit.lean.
