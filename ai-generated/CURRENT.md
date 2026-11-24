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

Lean and Mathlib v4.36.0 check all 60 current arbitrary-ring lower bounds, 45 of the 60 strongest characteristic-zero field entries, and 40 of the 60 strongest ordered-field and real entries. The counts include the stronger grade-five ERK proof. An entry is counted only if the checked theorem reaches the current established numerical endpoint, not merely a weaker lower bound.

- ERK: the generic characteristic-zero inequality gives 14 at order 10, 16 at order 11, and 19, 20, 22 at orders 13, 14, 15. It proves 17 at order 12; the stronger characteristic-zero bound of 18 is known mathematically but is not yet a completed Lean proof.
- DIRK: the ring theorem reaches the strongest characteristic-zero and ordered endpoint at every order through 11. Higher finite exclusions are still being formalized.
- Strict SDIRK: the complete current lower column is checked in all four settings, including the separate seven-stage bound at order six in characteristic zero. Over arbitrary rings the current order-six floor is six.

## Latest archived results

- [Order-19 ERK construction in 46 stages](upper-bounds/real-algebraic/erk_moving_helper_two_sided_causal_reciprocity_order19_46_20261123.md), with independent proof audit and exact replays.
- [Order-16 strict SDIRK construction in 38 stages](upper-bounds/real-algebraic/sdirk_order16_38_six_causal_entries_and_second_quadrature_reverse_20261123.md), with both literal stage merges and a complete exact replay.
- [Alternative order-16 DIRK construction in 27 stages](upper-bounds/real-algebraic/dirk_one_self_tapped_hermite_relay_p16_and_sharp_canonical_dense_stems_20261124.md). This confirms the same upper endpoint by a different exact construction.
- [Characteristic-zero ERK proof in Lean](lean/RKCert/ERKGradeFive.lean) and [characteristic-zero strict SDIRK order six](lean/RKCert/SDIRKOrderSix.lean).
- [Recent conditional and architecture-specific results](lower-bounds/conditional/README.md), kept separate from unrestricted numerical endpoints.
