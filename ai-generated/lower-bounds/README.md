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
| 8 | 10 / 8 / 10 | 11 / 8 / 10 | 11 / 8 / 10 |
| 9 | 12 / 10 / 13 | 12 / 10 / 13 | 13 / 10 / 13 |
| 10 | 14 / 11 / 15 | 14 / 11 / 15 | 14 / 11 / 15 |
| 11 | 17 / 13 / 18 | 17 / 13 / 18 | 17 / 13 / 18 |
| 12 | 18 / 15 / 21 | 18 / 15 / 21 | 18 / 15 / 21 |
| 13 | 20 / 17 / 25 | 20 / 17 / 25 | 20 / 17 / 25 |
| 14 | 21 / 19 / 28 | 21 / 19 / 28 | 21 / 19 / 28 |
| 15 | 23 / 20 / 32 | 23 / 21 / 32 | 23 / 21 / 32 |
| 16 | 24 / 21 / 36 | 24 / 22 / 36 | 25 / 22 / 36 |
| 17 | 26 / 23 / 41 | 27 / 24 / 41 | 27 / 24 / 41 |
| 18 | 27 / 25 / 45 | 28 / 25 / 45 | 29 / 25 / 45 |
| 19 | 30 / 27 / 50 | 30 / 27 / 50 | 30 / 27 / 50 |
| 20 | 31 / 28 / 55 | 31 / 29 / 55 | 32 / 29 / 55 |

Every real statement in the last column transfers by real-closed-field theory: for a fixed order and stage count the question is a finite rational-polynomial feasibility problem. The proof itself can still use properties of the reals. Neither real nor ordered feasibility implies an unordered characteristic-zero lower bound. The ring column uses uniform proofs and is not a claim that the stronger characteristic-zero bounds have counterexamples in positive characteristic.

- [Order-eight ERK without ordered coefficients](../research/erk-eight-unordered/README.md): eleven stages are necessary in every characteristic-zero field and nonzero characteristic-zero commutative ring. The full lower proof is mathematical, with a native physical bridge and scalar checks; positive-characteristic minimality is not asserted.
- [Transfer from separated stage residuals](paid-beta/separated-pure/README.md): the ERK lower bounds at orders 17–20 in characteristic zero are 27, 28, 30, and 31. The last two also hold over every nonzero commutative ring. This does not change the ordered-field bounds and is not yet formalized in Lean.
- [Weighted explicit stage bound](paid-beta/07-WEIGHTED-DETECTOR-STAGE-BOUND.md) and [order-eleven refinement](paid-beta/08-ORDER-ELEVEN-THRESHOLD.md): effective order \(r\ge11\) requires at least \(\lceil3r/2
ceil\) stages through the last contributing coefficient. For ordinary explicit methods this raises order 11 to 17 in all columns and the arbitrary-ring order-16 floor to 24. These are mathematical proofs, not Lean certificates.
- [Odd explicit orders from 13 onward](paid-beta/06-ODD-EXPLICIT-STAGE-BOUND.md): order \(2d+1\) requires at least \(3d+2\) stages for \(d\ge6\) over all nonzero commutative unital rings. This raises the arbitrary-ring bounds at 13, 15, and 17, and the characteristic-zero bounds at 13 and 15. The new proof is not yet formalized in Lean.
- [All-ring ERK lower bound: fifth-degree surplus](paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md) and [doubling surplus](paid-beta/02-PAID-DOUBLING-SURPLUS.md): the stronger entries at orders 10–20 are proved algebraically and have not yet been formalized in Lean.
- [Finite paid-field ERK argument at orders 18 and 19](paid-beta/03-PAID-ORDER-EIGHTEEN-NINETEEN.md): the arbitrary-ring floors equal the characteristic-zero values 27 and 29.
- [Paid order-14 ERK argument](paid-beta/04-PAID-ORDER-FOURTEEN.md): the arbitrary-ring floor matches the characteristic-zero value of 21. The proof uses two chronological root tests and an exact integer norm certificate.
- [Paid order-12 ERK proof](paid-beta/05-PAID-ORDER-TWELVE.md): ranks, physical stage order and the exact exceptional-prime calculation give the characteristic-zero floor of 18 over every nonzero commutative unital ring.
- [Paid DIRK grade-six argument](paid-beta/DIRK-PAID-GRADE-SIX.md): raises the arbitrary-ring lower bound by one for every order from 12 onward, matching the characteristic-zero entries at 12 and 13.
- [Paid DIRK order-fourteen proof](paid-beta/DIRK-PAID-ORDER-FOURTEEN.md): 19 stages over every nonzero commutative unital ring. The proof uses physical stage order and the two previously checked ERK norms.
- [Paid DIRK proof at orders 18 and 19](paid-beta/DIRK-PAID-ORDERS-EIGHTEEN-NINETEEN.md): 25 and 27 stages over every nonzero commutative unital ring, matching the characteristic-zero floors.
- [Paid DIRK order-twenty proof](paid-beta/DIRK-PAID-ORDER-TWENTY.md): 28 stages over every nonzero commutative unital ring. The proof combines the flat-band theorem with chronological separation on the first two off-support receivers.
- [Characteristic-zero arguments](characteristic-zero/README.md)
- [Ordered-field arguments and transfer](ordered-fields/README.md)
- [Proofs using the reals](real-proofs/README.md)
- [Conditional and construction-family exclusions](conditional/README.md)
- [Lean certificates](../lean/README.md)

- [Supporting proof dependencies and historical derivations](proof-dependencies/README.md)
