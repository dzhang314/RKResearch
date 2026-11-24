# Reducing the ten-stage explicit order-eight case

The hypothesis is an explicit ten-stage tableau satisfying the rooted-tree order conditions through order eight over a field of characteristic zero. An off abscissa is a distinct stage abscissa at which a stage residual of order two is nonzero. The Lean development sharpens the count of these abscissas:

- `RKCert.Paired.order8_no_five_off_nodes` excludes exactly five.
- `RKCert.Paired.order8_off_nodes_lt_seven` excludes seven or more, without a cancellation hypothesis on the aggregate weights.
- `RKCert.Paired.order8_off_count_one_or_four` combines these exclusions with the earlier structural reductions. The count is either one or four.

The proofs use the first physical stage satisfying the order-two stage condition, a fixed Lobatto interpolation polynomial, and an exact rational Bézout identity. The five-node case also uses the terminal coordinate vector in the fourth tree-weight space. The large-count case instead tests actual residual vectors against the product of the on-node and off-node polynomials.

Neither remaining count is excluded here. This chapter does not establish a new numerical lower bound.

Lean entry point: [`RKCert/ERKOrderEightLobatto.lean`](RKCert/ERKOrderEightLobatto.lean). Audit: [`AuditOrderEight.lean`](AuditOrderEight.lean).
