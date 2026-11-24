# Characteristic-zero DIRK lower bounds at orders 18 and 20
Pinned Lean and Mathlib v4.36.0. Order 18 requires at least 25 physical stages; order 20 requires at least 28. The former matches the strongest currently recorded order-18 lower bound. The latter is a checked intermediate, not the separately known 29-stage result. No attainability claim is made.

The public names are RKCert.Paired.dirk_order18_charZero_field, RKCert.dirk_order18_charZero_ring and the two matching order20 names. Their only inputs are a lower triangular physical tableau and genuine rooted-tree order at least 18 or 20. For the field forms the scalar requirements are Field and CharZero; for the ring forms CommRing and CharZero. There is no ordered-field, positivity, nonzero-weight, canonical quotient, distinct physical nodes, or common diagonal hypothesis.

An equality tableau at the older parity floor has a genuine jointly visible fifth-grade error. Original-array reverse pivots and the bound on the number of clean active sites turn it into a nonzero quintic Q at a nonzero grid root u with three paid primitive tests. Exact Lobatto cardinal reproduction forces Q to vanish at three distinct omitted grid knots. The remaining quadratic has a nonsingular 3×3 Hankel system. That finite certificate specializes only four scaled integral roots of a FIXED polynomial, using genuine integral extension and lying over. Neither Q nor the user's tableau is asserted integral or reduced. Homogeneity and symmetry reduce the two exact tables to respectively 840 and 1320 cases, including an allowed zero pivot residue (the original field pivot is nonzero). Checked by the ordinary Lean kernel with no native_decide, new axiom, or unverified numerical oracle.

Check the two leaf modules independently:
```sh
lake build RKCert.DirkOrder18Bound RKCert.DirkOrder20Bound
lake env lean AuditQuinticEndpoints.lean
lake env leanchecker RKCert.DirkOrder18Bound
lake env leanchecker RKCert.DirkOrder20Bound
```

The optional `replay_dirk_quintic.py` independently recomputes the finite determinants with the Python standard library. The Lean proof does not call it.
