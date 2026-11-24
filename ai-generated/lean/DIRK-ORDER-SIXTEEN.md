# Unconditional order-16 DIRK bound and the order-14 remaining singleton
Lean and Mathlib v4.36.0. The public names are RKCert.Paired.dirk_order16_charZero_field and RKCert.dirk_order16_charZero_ring. A lower triangular all-tree tableau over any characteristic-zero field or commutative ring needs at least 22 physical stages for order at least 16. No order, sign, separation, nonzero quadrature weights, or reduced-state equivalence is assumed. No construction or sharpness assertion.

On equality in the preceding parity floor, the actual midpoint decomposition is used through grade 2m−3. Its full scalar and orbit parameters are unique there, but higher pures need not automatically belong only to the orbit. The trace of a genuine product meeting both clean endpoints is a paid Lobatto tail. Full closed-grid divisibility follows whenever a scalar of degree at most q actually evaluates in the orbit, by polynomial division and an earned grade charge on the quotient. This puts every node-local product of two grade-five pures into the actual invariant summand. Its physical coordinate classes consequently produce an equally ranked head disjoint from its support. No stage is removed.

When r=2, w and clock*w are both paid at grade five, so w², clock*w² and clock²*w² are genuine grade-ten products. The actual scalar tails of all three vanish by their successive polynomial congruences. This proves the two-head contradiction simultaneously at order fourteen and sixteen with the physical polynomial-factor pivot and, for order fourteen, its grade-preserving shifted mask. When r=1 and m=8, the actual terminal cardinal supplies a nonzero cubic at the head; its product with the scalar part of w² is divisible by the closed grid, forcing the scalar part to vanish even without a second cheap head. Both branches at p16 are now impossible. At p14 this release states only the reduction to one genuine disjoint grade-five head, not the 19-stage endpoint.

The p14 theorem `RKCert.Paired.Terminal.order14_remaining_singleton` is a reduction, not an exclusion. The order-16 endpoint is independently reproducible from this directory:

```sh
lake build RKCert.DirkOrder16Bound
lake env lean AuditMidpoint16.lean
lake env leanchecker RKCert.DirkOrder16Bound
```
