# Exact explicit methods with factorial-unit coefficients

For each order below, the construction gives an explicit Runge–Kutta method with coefficients in any nonzero commutative ring in which the indicated factorial is a unit. The counts on the right are the number of rows in the literal tableaux after merging identical predecessor rows. They are upper bounds, not minima. The real-algebraic upper bounds are smaller and are unchanged.

| Order | Rows allocated by the proof | Rows after literal equality reduction |
|---:|---:|---:|
| 13 | 35 | [34](tableau-13.json) |
| 14 | 41 | [41](tableau-14.json) |
| 15 | 47 | [47](tableau-15.json) |
| 16 | 54 | [53](tableau-16.json) |
| 17 | 60 | [59](tableau-17.json) |
| 18 | 67 | [66](tableau-18.json) |
| 19 | 73 | [72](tableau-19.json) |
| 20 | 81 | [81](tableau-20.json) |

The [proof](CONSTRUCTION.md) uses a short reverse chart and two copies of each donor, with weights +1 and −1. The two copies have identical reverse reads, so their contributions cancel in the adjoint order calculation. Only the copy of weight +1 supplies donor columns. The other copy has a pure primitive row in the forward tableau and merges with an existing row at its clock. The resulting proof covers all rooted order conditions at all eight orders. A prescribed vanishing moment gives a next-order bush defect of −1; no inverse of the next order is used.

- `python construct.py 13` rebuilds the literal JSON for order 13, using exact rational arithmetic and the pinned order-nine seed. The other orders use the same command with a different number.
- `python verify.py 13 --all` and `python verify.py 14 --all` replay all 20,299 and 53,272 rooted conditions respectively, using exact integer arithmetic.
- `python verify.py 15` through `python verify.py 20` perform sampled replays. The complete proof at these orders is symbolic. All eight verifier runs also check the tree of the next order whose defect is −1.

This is not a new Lean certificate.
