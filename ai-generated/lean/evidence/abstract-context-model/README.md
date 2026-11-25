# Abstract rooted-series context model

The [Lean body](../../RKCert/ReviewedNative/AbstractContextModel.lean)
defines literal rooted-tree columns in a commutative algebra over a field.
A linear map acts along edges, multiplication combines branches at a root,
and a second linear map gives the scalar output. Inserting a tree into
a one-hole context agrees with the corresponding sequence of algebra
operations on its column.

The denominator-cleared order conditions determine each context/tree entry
whose inserted tree is within the chosen order. The rank of any finite
rectangular context/tree matrix is at most the dimension of the algebra.
Neither statement assumes coordinatewise stage multiplication or a split
stage representation. This certificate does not construct a
[full-board completion](../../../research/canonical-rk-realization/CONTEXT-MATRIX-COMPLETIONS.md)
or give a bound on the number of stages of an actual tableau.

The body and [no-output typed audit](../../AuditAbstractContextModel.lean)
both exited zero under Lean 4.36.0 and the Mathlib pin in
[acceptance.tsv](acceptance.tsv). The audit elaborated five client examples.
Its [unmodified output](typed-audit-output.txt) contains eight named type
checks and five named reports using only the stock axioms propext,
Classical.choice, and Quot.sound. The [actual axiom lists](actual-axioms.tsv)
and [ten project providers](reviewed-providers.sha256) are recorded
separately. No compiled objects are included.
