# Exact explicit methods with factorial-unit coefficients

For each order below, the construction gives an explicit Runge–Kutta method with coefficients in any nonzero commutative ring in which the indicated factorial is a unit. The counts on the right are the number of rows in the literal tableaux after merging identical predecessor rows. They are upper bounds, not minima. The real-algebraic upper bounds are smaller and are unchanged.

| Order | Rows allocated by the proof | Rows after literal equality reduction |
|---:|---:|---:|
| 11 | 27 | [25](tableau-11.json) |
| 12 | 30 | [28](tableau-12.json) |
| 13 | 34 | [33](tableau-13.json) |
| 14 | 38 | [37](tableau-14.json) |
| 15 | 44 | [44](tableau-15.json) |
| 16 | 51 | [50](tableau-16.json) |
| 17 | 58 | [57](tableau-17.json) |
| 18 | 64 | [63](tableau-18.json) |
| 19 | 72 | [71](tableau-19.json) |
| 20 | 79 | [79](tableau-20.json) |

The [proof](CONSTRUCTION.md) uses a short reverse chart and two copies of each donor, with weights +1 and −1. The two copies have identical reverse reads, so their contributions cancel in the adjoint order calculation. Only the copy of weight +1 supplies donor columns. The other copy has a pure primitive row in the forward tableau and merges with an existing row at its clock. The [shorter scalar grids](SHORT-SYMMETRIC-GRIDS.md) use one or two next-order defects to show exact order, without needing an inverse of the next order. Order eleven uses the [eight-row reverse chart through size five](SHARP-PAID-ERK-GRADE-FIVE.md).

- `python construct.py 13` rebuilds the literal JSON for order 13, using exact rational arithmetic and the pinned order-nine seed. The other orders use the same command with a different number.
- `python verify.py 11 --all` through `python verify.py 14 --all` replay every rooted condition at the specified order, using exact integer arithmetic.
- `python verify.py 15` through `python verify.py 20` perform sampled replays. The complete proof of order at these orders is symbolic. All ten verifier runs also verify exactness at the next order.

This is not a new Lean certificate.

The [shorter order-seven chart](SHORT-GRADE-SEVEN.md) uses an exact contrast of three old stage derivatives, reducing its preparation from sixteen rows to fifteen. It is used on both sides at order fifteen, saving two stages there, and on one side at orders fourteen, sixteen, and seventeen.

The [projected order-eighteen construction](PROJECTED-ORDER-18.md) saves another stage by omitting an irrelevant reverse polynomial. The projection verifier checks every rooted chart condition through size nine on the two actual prefixes.
