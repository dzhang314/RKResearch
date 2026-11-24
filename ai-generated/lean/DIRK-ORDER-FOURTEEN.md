# Unconditional DIRK order 14 over characteristic-zero fields and rings
Every lower-triangular all-tree tableau of order ≥14 over a characteristic-zero field or commutative ring uses at least 19 original physical stages. The two public names in RKCert.DirkOrder14Bound are RKCert.Paired.dirk_order14_charZero_field and RKCert.dirk_order14_charZero_ring. There is no ordering, positivity, full-support, reduced-array or attainability condition.

The rank floor leaves only an 18-stage equality chart. The prior midpoint physical release forced a single surviving alternative: an actual invariant coordinate algebra U inside F5 and one genuine head through F5,F6,F7, after excluding the two-cheap-head branch. The independently certified refunded fifth-debut obstruction proves that the remaining one-head alternative cannot occur even at order ten. Combining these two actual order-14 branches and the characteristic-zero residue-field transfer gives the stated stage bound. No hidden coordinate was dropped.

The [fifth-debut proof](REFUNDED-FIFTH-DEBUT.md) separates the physical tableau argument from [the scalar contradiction](FIVE-DEBUT-SCALAR.md). Replay the endpoint under Lean and Mathlib v4.36.0:
```sh
lake build RKCert.DirkOrder14Bound
lake env lean AuditDIRKOrder14.lean
lake env leanchecker RKCert.DirkOrder14Bound
```
