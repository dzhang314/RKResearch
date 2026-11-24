# Lower bounds and proof fields

The table lists ERK / DIRK / strict SDIRK for each order. Rings are nonzero commutative unital rings; strict SDIRK uses a unit common diagonal at this level. The field column ranges over all characteristic-zero fields, not just subfields of the reals.

| Order | Any commutative ring | Any characteristic-zero field | Any ordered field, including ℝ |
|---:|:---:|:---:|:---:|
| 1 | 1 / 1 / 1 | 1 / 1 / 1 | 1 / 1 / 1 |
| 2 | 2 / 1 / 1 | 2 / 1 / 1 | 2 / 1 / 1 |
| 3 | 3 / 2 / 2 | 3 / 2 / 2 | 3 / 2 / 2 |
| 4 | 4 / 3 / 3 | 4 / 3 / 3 | 4 / 3 / 3 |
| 5 | 6 / 4 / 5 | 6 / 4 / 5 | 6 / 4 / 5 |
| 6 | 7 / 5 / 6 | 7 / 5 / 7 | 7 / 5 / 7 |
| 7 | 9 / 7 / 8 | 9 / 7 / 8 | 9 / 7 / 8 |
| 8 | 10 / 8 / 10 | 10 / 8 / 10 | 11 / 8 / 10 |
| 9 | 12 / 10 / 13 | 12 / 10 / 13 | 13 / 10 / 13 |
| 10 | 13 / 11 / 15 | 14 / 11 / 15 | 14 / 11 / 15 |
| 11 | 15 / 13 / 18 | 16 / 13 / 18 | 16 / 13 / 18 |
| 12 | 16 / 14 / 21 | 18 / 15 / 21 | 18 / 15 / 21 |
| 13 | 18 / 16 / 25 | 19 / 17 / 25 | 20 / 17 / 25 |
| 14 | 19 / 17 / 28 | 20 / 19 / 28 | 21 / 19 / 28 |
| 15 | 21 / 19 / 32 | 22 / 21 / 32 | 23 / 21 / 32 |
| 16 | 22 / 20 / 36 | 24 / 22 / 36 | 25 / 22 / 36 |
| 17 | 24 / 22 / 41 | 26 / 23 / 41 | 27 / 24 / 41 |
| 18 | 25 / 23 / 45 | 27 / 25 / 45 | 29 / 25 / 45 |
| 19 | 27 / 25 / 50 | 29 / 27 / 50 | 30 / 27 / 50 |
| 20 | 28 / 26 / 55 | 30 / 29 / 55 | 32 / 29 / 55 |

Every real statement in the last column transfers by real-closed-field theory: for a fixed order and stage count the question is a finite rational-polynomial feasibility problem. The proof itself can still use properties of the reals. Neither real nor ordered feasibility implies an unordered characteristic-zero lower bound. The ring column uses uniform proofs and is not a claim that the stronger characteristic-zero bounds have counterexamples in positive characteristic.

- [Characteristic-zero arguments](characteristic-zero/README.md)
- [Ordered-field arguments and transfer](ordered-fields/README.md)
- [Proofs using the reals](real-proofs/README.md)
- [Conditional and construction-family exclusions](conditional/README.md)
- [Lean certificates](../lean/README.md)

- [Supporting proof dependencies and historical derivations](proof-dependencies/README.md)
