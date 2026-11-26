# Exact explicit methods with factorial-unit coefficients

For each order below, the construction gives an explicit Runge–Kutta method with coefficients in any nonzero commutative ring in which the indicated factorial is a unit. The counts on the right are the number of rows in the literal tableaux after merging identical predecessor rows. They are upper bounds, not minima. The real-algebraic upper bounds are smaller and are unchanged.

| Order | Rows allocated by the proof | Rows after literal equality reduction |
|---:|---:|---:|
| 11 | 23 | [23](tableau-11-weighted.json) |
| 12 | 25 | [25](order-12-factorial-25/tableau-12-factorial-25.json) |
| 13 | 30 | [30](tableau-13-weighted.json) |
| 14 | 33 | [33](tableau-14-weighted.json) |
| 15 | 39 | [39](order-15-factorial-39/tableau-15-factorial-39.json) |
| 16 | 45 | [45](tableau-16-weighted.json) |
| 17 | 51 | [51](order-17-factorial-51/tableau-17-factorial-51.json) |
| 18 | 57 | [57](order-18-factorial-57/tableau-18-factorial-57.json) |
| 19 | 64 | [64](order-19-factorial-64/tableau-19-factorial-64.json) |
| 20 | 70 | [70](order-20-factorial-70/tableau-20-factorial-70.json) |

The [proof](CONSTRUCTION.md) uses a short reverse chart and two copies of each donor, with weights +1 and −1. The two copies have identical reverse reads, so their contributions cancel in the adjoint order calculation. Only the copy of weight +1 supplies donor columns. The other copy has a pure primitive row in the forward tableau and merges with an existing row at its clock. The [shorter scalar grids](SHORT-SYMMETRIC-GRIDS.md) use one or two next-order defects to show exact order, without needing an inverse of the next order. Order eleven uses the [eight-row reverse chart through size five](SHARP-PAID-ERK-GRADE-FIVE.md).

- `python construct.py 13` rebuilds the literal JSON for order 13, using exact rational arithmetic and the pinned order-nine seed. The original tableaux at the other orders use the same command with a different number. The current tableaux at orders 12, 15, 17, 18, 19, and 20 have separate constructors below.
- `python verify.py 11 --all` through `python verify.py 14 --all` replay every rooted condition at the specified order, using exact integer arithmetic.
- `python verify.py 15` through `python verify.py 20` perform sampled replays. The complete proof of order at these orders is symbolic. All ten verifier runs also verify exactness at the next order.

This is not a new Lean certificate.

The [shorter order-seven chart](SHORT-GRADE-SEVEN.md) uses an exact contrast of three old stage derivatives, reducing its preparation from sixteen rows to fifteen. It is used on both sides at order fifteen, saving two stages there, and on one side at orders fourteen, sixteen, and seventeen.

The [projected order-eighteen construction](PROJECTED-ORDER-18.md) saves another stage by omitting an irrelevant reverse polynomial. The projection verifier checks every rooted chart condition through size nine on the two actual prefixes.

At order twenty, [putting the larger chart on the reverse side](REFLECTED-ORDER-20.md) restores a literal endpoint merger and reduces the tableau to 78 stages. The separate chart verifier checks both complete decoders.

The [prescribed-node variant](PRESCRIBED-NODE-GRIDS.md) uses 70 stages at order nineteen over the rationals. Its extra site gaps need not be units in the factorial localization; it is distinct from the constructions with factorial-unit coefficients.

At order seventeen, [weighted regular probes](WEIGHTED-REGULAR-PROBES.md) use existing scalar sites for a collective measurement of the reverse defect. The weights need not be units individually. The first version reduces the tableau to 56 stages.

[Weighted regular probes at orders 18–20](WEIGHTED-ORDERS-18-20.md) gave 62-, 68-, and 75-stage tableaux by solving for missing reverse directions from existing scalar sites. The earlier tableaux can still be rebuilt and checked with the explicit historical option.

[Direct weighted site recovery](WEIGHTED-SITE-RANK.md) uses maximal-minor certificates for the weighted evaluations. This version gave 53, 60, 66, and 72 stages at orders 17–20. At order 20, [recovering only the forward pairings](order-20-factorial-71/README.md) frees a scalar site for reverse recovery and improves the bound to 71 with no extra inversions. At order 19, [the same pairing reduction and a shorter reverse chart](order-19-factorial-65/README.md) improve the bound to 65. At order 17, [pairing the order-18 forward chart with the order-15 reverse chart](order-17-factorial-52/README.md) improves the bound to 52. At order 17, [two-tier weighted recovery](order-17-factorial-51/README.md) shortens that same reverse chart by another stage. The earlier 52-, 53-, 66-, and 72-stage tableaux remain unchanged.

[Weighted probes at orders 11–16](WEIGHTED-ORDERS-11-16.md) use a common three-size family of short reverse charts. The earlier constructions at these orders remain available through the historical option.

At order twelve, [combining the nine-row forward chart with the eight-row reverse chart](order-12-factorial-25/README.md) gives 25 stages and verifies exact order without inverting 13. The former 26-stage tableau is unchanged.

At order 15, [two tiers of weighted receivers](order-15-factorial-39/README.md) recover the missing donor direction in 39 stages instead of 40. The checker verifies the additional intermediate source pairing as well as the final one. The [40-stage tableau and its compact certificate](order-15-certificate/README.md) remain available.

At order 20, [two-mode recovery on twenty asymmetric scalar nodes](order-20-factorial-70/README.md) drops two reverse donors while adding just one scalar row. The former 71-stage tableau remains unchanged.

At order 19, [an asymmetric scalar grid and two-tier weighted recovery](order-19-factorial-64/README.md) reduce the factorial-unit count from 65 to 64. The asymmetric grid ensures that no unpaid prime removes two live measurements.

At order 18, [combining the order-20 forward chart with the order-15 reverse chart](order-18-factorial-57/README.md) gives 57 stages. Seven pure sites and eight weighted receiver sites pay separate interpolation tests. No inverse of 19 or other extra prime is needed. The [59-stage localized](order-18-localized-59/README.md) and [60-stage factorial-unit](order-18-certificate/README.md) tableaux remain available.
