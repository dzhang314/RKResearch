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

## Exact explicit minima over nonzero commutative rings

- [Order five](research/erk-five-ring-witness/README.md): six stages are necessary and sufficient if 120 is a unit. Otherwise no stage count attains order five.
- [Order six](research/erk-six-ring-minimum/README.md): seven stages are necessary and sufficient if 720 is a unit. A single rational tableau specializes to every such ring, including positive characteristic. This supersedes the eight-stage construction as a minimum, not as a denominator-removal technique.

- [Order seven](research/erk-seven-ring-witness/README.md): order seven is possible exactly when 5040 is a unit. The uniform stage count is between nine and ten; the ten-stage tableau reuses a Shanks endpoint to remove an extra denominator. The nine-stage universal question is open in this project.

The lower bounds are covered by the uniform Lean theorem. The three upper tableaux have exact arithmetic checks; this does not add Lean coverage for their constructions. The real-algebraic numerical table above is unchanged.

## Rational contributing quadrature support

Separate from the stage tables, the [four-shift proof](research/rational-quadrature-four-shift/proof.md) gives at least \(\min(17,p-3)\) distinct contributing rational sites for quadrature order \(p\ge4\): 16 at order 19 and 17 at order 20. Weights may be arbitrary in a characteristic-zero field. Repeat sites are grouped first, and only nonzero aggregate weights count. The result transfers to Runge–Kutta by the reviewed bushy moments. It has an exact arithmetic check, not a new Lean certificate.

A [standalone 19-site rational rule](research/rational-quadrature-four-shift/standalone-19.md) attains quadrature order 20 with positive weights. This is not a Runge–Kutta stage upper bound. The [support index](research/rational-quadrature-four-shift/README.md) retains the stronger earlier low-order bounds.

The [donor realization theorem](research/quadrature-donor-realization/realization.md) goes in the other direction: every scalar rule of order at least \(p\) lifts to ERK, DIRK, or strict SDIRK with a prescribed common diagonal, preserving its contributing sites and weights. The same \(u/128\) rule gives tableaux of exact order 20 with 19 contributing sites and 209 physical rows, including 190 zero-output helpers. This equates the minimal contributing support with the scalar minimum, not the minimum stage count. No stage bound or Lean coverage count changes.

A separate [radii/33 prescribed-support realization](research/rational-support-radii33-splice/realization.md) keeps another 19-site rational rule's positive aggregate weights and has exact order 20 in 101 physical rows for ERK and 117 for strict SDIRK with common diagonal \(1/66\). This is not the \(u/128\) rule. The counts do not change the global stage tables; the proof and deterministic replay add no Lean coverage claim.

The [ordered-root geometry](research/rational-root-chart-geometry/ordered-root-geometry.md) gives a structural obstruction, not a support exclusion: with two or three paid nodal shifts the positive-dimensional smooth root charts have no dominant rational parametrization. A generic fixed prefix leaving one free root beyond Hankel completion gives a genus-one or genus-13 curve, respectively. The geometry alone does not decide attainability. It does not change a stage bound or Lean coverage.

The [two-shift elliptic criterion](research/two-shift-elliptic-transfer/elliptic-transfer.md) tests fixed-prefix completions exactly. A same-gap lower rule of exact order supplies rational infinity points and a conditional rank-free candidate. Neither of the known 19-site order-20 rules supplies the needed order-19 seed.

The [fixed-functional same-gap ladder](research/same-gap-seed-ladder/seed-ladder.md) shows that a genuine rational two-shift seed with a nontorsion completion pair can raise exact order and support repeatedly without changing the moments. The [uniform seed below](research/uniform-same-gap-seed/uniform-seed.md) meets that hypothesis.

## Lean certificate coverage

Lean and Mathlib v4.36.0 check all 60 current arbitrary-ring lower bounds, all 60 strongest characteristic-zero field entries, and 56 of the 60 strongest ordered-field and real entries. The characteristic-zero count includes the ERK exclusions at orders 12, 14 and 16–19, and the characteristic-zero DIRK exclusions at orders 14 and 16–20. An entry is counted only if the checked theorem reaches the current established numerical endpoint, not merely a weaker lower bound.

- ERK: the [ordered order-nine certificate](lean/ERK-ORDER-NINE-ORDERED.md) reaches 13 stages. The generic characteristic-zero inequality gives 14 at order 10, 16 at order 11, and 22 at order 15. The [integrated ordered-field certificate](lean/INTEGRATED-ORDER15-17.md) reaches 23 at order 15. The [native order-17 proof](lean/RKCert/ReviewedNative/ERK17OrderedStageFloor27Native.lean) certifies 27 stages directly on the reviewed order predicate, using a [kernel-checked residue argument](lean/evidence/reviewed-native-erk17-floor27-20261125/README.md). The [ordered order-13 certificate](lean/ERK-ORDER-THIRTEEN.md) proves at least 20 stages, versus 19 over unordered characteristic-zero fields. The [order-14 proof](lean/ORDER-FOURTEEN.md) improves the characteristic-zero floor from 20 to 21, matching the ordered-field result. The [order-12 exclusion](lean/ORDER_TWELVE.md) proves the strongest characteristic-zero bound of 18. The [finite order-16 through order-19 proof](lean/FINITE-ERK16-19.md) certifies 24, 26, 27 and 29 characteristic-zero stages, respectively. The [ordered order-19 certificate](lean/RKCert/ReviewedNative/ERK19OrderedFloor30.lean) proves at least 30 stages over every ordered field. The [logarithmic refinement](lean/RKCert/ERKLogarithmic.lean) proves 30 at order 20 in characteristic zero; it does not certify the stronger ordered-field floor of 32.
- DIRK: the ring theorem reaches the strongest characteristic-zero and ordered endpoint at every order through 11. The [grade-six proof](lean/RKCert/DirkGradeSix.lean) also reaches the current strongest floors of 15 and 17 at orders 12 and 13 over characteristic-zero rings. The [parity theorem](lean/DIRK-PARITY.md) gives 23 at order 17. The [stronger order-17 certificate](lean/DIRK-ORDER-SEVENTEEN.md) gives 24 over every characteristic-zero field and commutative ring, not just ordered fields. The [order-14 proof](lean/DIRK-ORDER-FOURTEEN.md) certifies 19 stages. The [order-16 proof](lean/DIRK-ORDER-SIXTEEN.md) certifies 22 stages. The [quintic certificate](lean/DIRK-ORDER18-20.md) reaches the current floor of 25 at order 18. The [order-19 proof](lean/ORDER-19-CHARACTERISTIC-ZERO.md) certifies 27 stages. The [final order-20 certificate](lean/DIRK-ORDER-TWENTY.md) reaches 29 stages, superseding the intermediate Lean bound of 28. The [order-15 certificate](lean/INTEGRATED-ORDER15-17.md) proves at least 21 stages over every characteristic-zero field and commutative ring.
- Strict SDIRK: the complete current lower column is checked in all four settings, including the separate seven-stage bound at order six in characteristic zero. Over arbitrary rings the current order-six floor is six.

## General bounds beyond order 20

The [even-order DIRK certificate](lean/DIRK-EVEN-FROM-22.md) proves at least \(3m-2\) stages for order \(2m\) with \(m\ge 11\), over any characteristic-zero field or commutative characteristic-zero ring. In particular order 22 needs at least 31 stages. This result does not change the table through order 20.

## Latest archived results

- [Lean certificate for the four-shift rational support lower bound](lean/evidence/dyadic-rational-support-four-shift/README.md): at least 17 contributing rational sites at order 20, with arbitrary weights in any characteristic-zero field.

- [Lean certificate for the finite tall-response degree bound](lean/evidence/tall-derivative-gcd-quotient/README.md): over characteristic-zero fields, the paid order is at most the numerator degree plus the degree of the denominator divided by its derivative gcd. The certificate does not formalize the geometric root count or change a stage entry.

- [Lean certificate for the conditional order-20 four-clock count of 28](lean/evidence/order20-four-clock-counted28/README.md): the directed cut must have trivial kernel intersection on the counted side. No unrestricted stage entry changes.

- [Explicit exact order-20 rule on 18 rational sites](research/uniform-order20-slp/order20-slp.md): fixed rational formulas and checked arithmetic, with the fractions unexpanded. Signed weights are allowed and the rule includes the exterior site −3/32. A 17-site rule remains open; no stage or Lean upper bound changes.

- [Rational quadrature on \(p-2\) contributing sites for every \(p\ge12\)](research/uniform-same-gap-seed/uniform-seed.md): signed weights and unrestricted rational nodes. Order 20 now needs 17 or 18 sites in this setting. A [separate exact order-14 seed](research/uniform-interval-same-gap-seed/interval-seed.md) uses 12 sites in the interval, without a positivity or interval-preserving iteration claim.

- [Lean certificate for the order-16 ERK lower bound of 25 stages](lean/evidence/erk16-ordered-stage-floor25/README.md): holds over any ordered field for the reviewed order conditions, without a hypothesis about quadrature nodes or weights.

- [Lean certificate for 11-stage strict SDIRK at order eight](lean/evidence/reviewed-native-sdirk118-witness-20261125/README.md): the positive common diagonal and all order conditions are proved over the reals. A [second Lean certificate](lean/evidence/reviewed-native-sdirk118-number-field-20261125/README.md) lifts the same tableau to a coefficient field of degree at most 12 over the rationals.

- [Lean certificate for rational 15-stage strict SDIRK of exact order eight](lean/evidence/reviewed-native-rational-sdirk-fifteen-stage-eight-20261125/README.md): common nonzero diagonal `1/8`, with the exact ninth tall-tree failure. This is a rational upper witness, not a minimum or a change to the real-algebraic 11-stage upper bound.
- [Lean certificate for rational 23-stage strict SDIRK of exact order nine](lean/evidence/reviewed-native-rational-sdirk-twenty-three-stage-nine-20261125/README.md): common nonzero diagonal 1/9, with the exact tenth tall-tree failure. This is a rational upper witness, not a stage minimum.
- [Exact arithmetic certificate for rational 27-stage strict SDIRK of exact order ten](upper-bounds/rational/strict-sdirk-order-ten-27/README.md): common nonzero diagonal 1/9, with the exact eleventh tall-tree failure. The Lean certificate is pending; the real-algebraic upper bound and Lean coverage are unchanged.


- [Lean certificate for exact ten-stage DIRK at order nine](lean/evidence/reviewed-native-dirk-nine-sharp-c35/README.md): ten stages are necessary and sufficient over the reals and real algebraic numbers. The [exact tableau](lean/evidence/reviewed-native-dirk-nine-exact-c35/README.md) also fails the order-ten tall-tree condition.
- [Order-19 ERK construction in 46 stages](upper-bounds/real-algebraic/erk_moving_helper_two_sided_causal_reciprocity_order19_46_20261123.md), with independent proof audit and exact replays.
- [Order-16 strict SDIRK construction in 38 stages](upper-bounds/real-algebraic/sdirk_order16_38_six_causal_entries_and_second_quadrature_reverse_20261123.md), with both literal stage merges and a complete exact replay.
- [Alternative order-16 DIRK construction in 27 stages](upper-bounds/real-algebraic/dirk_one_self_tapped_hermite_relay_p16_and_sharp_canonical_dense_stems_20261124.md). This confirms the same upper endpoint by a different exact construction.
- [Characteristic-zero ERK proof in Lean](lean/RKCert/ERKGradeFive.lean) and [characteristic-zero strict SDIRK order six](lean/RKCert/SDIRKOrderSix.lean).
- [Recent conditional and architecture-specific results](lower-bounds/conditional/README.md), kept separate from unrestricted numerical endpoints.

- [Simplified reverse proof for order 12](lean/REVERSE_OBSTRUCTION.md) and [finite-exception characteristic transfer](lower-bounds/CHARACTERISTIC-TRANSFER.md).
