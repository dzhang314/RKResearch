# Twelve stages at order eight over all admissible fields and in positive characteristic

If 8! is a unit, a nontrivial commutative ring of positive characteristic
admits a twelve-stage explicit Runge–Kutta method of **exact order eight**.
This includes composite characteristic and rings with nilpotents. The same
upper bound holds in any field in which 8! is a unit, without an ordered-field
hypothesis.

- When 41 is a unit, use the original unsplit twelve-stage
  [Shanks tableau](https://doi.org/10.1090/S0025-5718-1966-0187406-1).
  Its common denominator is 139482000; the normalized ninth-bush
  discrepancy is 1/4320.
- When a square root of 21 exists, the eleven-stage
  [Cooper–Verner tableau](https://doi.org/10.1137/0709037) works without
  dividing by 41. Its common denominator is 282240 and the same
  discrepancy is 1/3920. In particular the root 12 works in characteristic 41.

For positive characteristic v, write v = 41^k m with 41 not dividing m.
Invertibility of 8! implies that v is coprime to 210. The 41-power factor
has a root of 21: iterate x ↦ x − 12(x²−21) from x=12. The root error
gains at least one factor of 41 each step, without division, because
x stays congruent to 12 modulo 41. Use the padded Cooper–Verner tableau
on that factor and Shanks on the coprime factor. Combine them by the
Chinese remainder ring isomorphism, then map into the coefficient ring.
Both component discrepancies on the ninth bush are units, hence exact
order is preserved. A characteristic-zero field uses Shanks directly.

This does not give a twelve-stage tableau over arbitrary characteristic-zero
rings in which 41 need not be a unit, such as the universal factorial
localization. The prior thirteen-stage bound for arbitrary admissible
rings and the eleven-stage real-algebraic upper remain unchanged.

Run `python3 check.py` here for an independent exact replay of all 200
unordered trees through order eight for both charts and the specialization
modulo 41. The Lean proofs use the native reviewed order predicate and check
both charts on all 626 ordered constructor trees with the kernel, then
prove the coefficient maps, unit discrepancy, padding, root lift, and
Chinese remainder combination.

```sh
# From ai-generated/lean, with matching Lean and Mathlib.
lake build RKCert.ReviewedNative.ERK8FiniteCharacteristic
```

Main declarations: `positive_characteristic_factorial` and
`all_fields_factorial` in `RKResearch.Certified.ERK8FiniteCharacteristic`.
