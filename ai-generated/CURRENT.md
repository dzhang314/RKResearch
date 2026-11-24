# Current state of knowledge

## Real and ordered-field lower bounds, with real-algebraic upper bounds

| Order | ERK | DIRK | Strict SDIRK |
|---:|:---:|:---:|:---:|
| 1 | 1 | 1 | 1 |
| 2 | 2 | 1 | 1 |
| 3 | 3 | 2 | 2 |
| 4 | 4 | 3 | 3 |
| 5 | 6 | 4 | 5 |
| 6 | 7 | 5 | 7 |
| 7 | 9 | 7 | 8–9 |
| 8 | 11 | 8 | 10–11 |
| 9 | 13 | 10 | 13–14 |
| 10 | 14–15 | 11–12 | 15–17 |
| 11 | 16–18 | 13–14 | 18–20 |
| 12 | 18–21 | 15–16 | 21–23 |
| 13 | 20–23 | 17–18 | 25–26 |
| 14 | 21–26 | 19–21 | 28–30 |
| 15 | 23–31 | 21–24 | 32–34 |
| 16 | 25–34 | 22–27 | 36–38 |
| 17 | 27–38 | 24–30 | 41–43 |
| 18 | 29–42 | 25–34 | 45–48 |
| 19 | 30–46 | 27–38 | 50–54 |
| 20 | 32–51 | 29–42 | 55–59 |

The lower bounds apply to all ordered fields. A construction over the real algebraic numbers need not be defined over every ordered subfield. For conclusions over arbitrary rings or unordered characteristic-zero fields, see the [lower-bound table](lower-bounds/README.md).

## Lean certificate coverage

Lean and Mathlib v4.36.0 check all 60 current arbitrary-ring lower bounds, all 60 strongest characteristic-zero field entries, and 56 of the 60 strongest ordered-field and real entries. The characteristic-zero count includes the ERK exclusions at orders 12, 14 and 16–19, and the characteristic-zero DIRK exclusions at orders 14 and 16–20. An entry is counted only if the checked theorem reaches the current established numerical endpoint, not merely a weaker lower bound.

- ERK: the [ordered order-nine certificate](lean/ERK-ORDER-NINE-ORDERED.md) reaches 13 stages. The generic characteristic-zero inequality gives 14 at order 10, 16 at order 11, and 22 at order 15. The [integrated ordered-field certificates](lean/INTEGRATED-ORDER15-17.md) reach 23 at order 15 and 27 at order 17. The [ordered order-13 certificate](lean/ERK-ORDER-THIRTEEN.md) proves at least 20 stages, versus 19 over unordered characteristic-zero fields. The [order-14 proof](lean/ORDER-FOURTEEN.md) improves the characteristic-zero floor from 20 to 21, matching the ordered-field result. The [order-12 exclusion](lean/ORDER_TWELVE.md) proves the strongest characteristic-zero bound of 18. The [finite order-16 through order-19 proof](lean/FINITE-ERK16-19.md) certifies 24, 26, 27 and 29 characteristic-zero stages, respectively. The [ordered order-19 certificate](lean/RKCert/ReviewedNative/ERK19OrderedFloor30.lean) proves at least 30 stages over every ordered field. The [logarithmic refinement](lean/RKCert/ERKLogarithmic.lean) proves 30 at order 20 in characteristic zero; it does not certify the stronger ordered-field floor of 32.
- DIRK: the ring theorem reaches the strongest characteristic-zero and ordered endpoint at every order through 11. The [grade-six proof](lean/RKCert/DirkGradeSix.lean) also reaches the current strongest floors of 15 and 17 at orders 12 and 13 over characteristic-zero rings. The [parity theorem](lean/DIRK-PARITY.md) gives 23 at order 17. The [stronger order-17 certificate](lean/DIRK-ORDER-SEVENTEEN.md) gives 24 over every characteristic-zero field and commutative ring, not just ordered fields. The [order-14 proof](lean/DIRK-ORDER-FOURTEEN.md) certifies 19 stages. The [order-16 proof](lean/DIRK-ORDER-SIXTEEN.md) certifies 22 stages. The [quintic certificate](lean/DIRK-ORDER18-20.md) reaches the current floor of 25 at order 18. The [order-19 proof](lean/ORDER-19-CHARACTERISTIC-ZERO.md) certifies 27 stages. The [final order-20 certificate](lean/DIRK-ORDER-TWENTY.md) reaches 29 stages, superseding the intermediate Lean bound of 28. The [order-15 certificate](lean/INTEGRATED-ORDER15-17.md) proves at least 21 stages over every characteristic-zero field and commutative ring.
- Strict SDIRK: the complete current lower column is checked in all four settings, including the separate seven-stage bound at order six in characteristic zero. Over arbitrary rings the current order-six floor is six.

## General bounds beyond order 20

The [even-order DIRK certificate](lean/DIRK-EVEN-FROM-22.md) proves at least \(3m-2\) stages for order \(2m\) with \(m\ge 11\), over any characteristic-zero field or commutative characteristic-zero ring. In particular order 22 needs at least 31 stages. This result does not change the table through order 20.

## Latest archived results

- [Lean certificate for exact ten-stage DIRK at order nine](lean/evidence/reviewed-native-dirk-nine-sharp-c35/README.md): ten stages are necessary and sufficient over the reals and real algebraic numbers. The [exact tableau](lean/evidence/reviewed-native-dirk-nine-exact-c35/README.md) also fails the order-ten tall-tree condition.
- [Order-19 ERK construction in 46 stages](upper-bounds/real-algebraic/erk_moving_helper_two_sided_causal_reciprocity_order19_46_20261123.md), with independent proof audit and exact replays.
- [Order-16 strict SDIRK construction in 38 stages](upper-bounds/real-algebraic/sdirk_order16_38_six_causal_entries_and_second_quadrature_reverse_20261123.md), with both literal stage merges and a complete exact replay.
- [Alternative order-16 DIRK construction in 27 stages](upper-bounds/real-algebraic/dirk_one_self_tapped_hermite_relay_p16_and_sharp_canonical_dense_stems_20261124.md). This confirms the same upper endpoint by a different exact construction.
- [Characteristic-zero ERK proof in Lean](lean/RKCert/ERKGradeFive.lean) and [characteristic-zero strict SDIRK order six](lean/RKCert/SDIRKOrderSix.lean).
- [Recent conditional and architecture-specific results](lower-bounds/conditional/README.md), kept separate from unrestricted numerical endpoints.

- [Simplified reverse proof for order 12](lean/REVERSE_OBSTRUCTION.md) and [finite-exception characteristic transfer](lower-bounds/CHARACTERISTIC-TRANSFER.md).
