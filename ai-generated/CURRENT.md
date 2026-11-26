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

## Improved ERK lower bounds over arbitrary rings

The [paid Beta-moment argument](lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md) raises the arbitrary-ring ERK floors at orders 10 through 17 by at least one stage. At order 12 the [full paid proof](lower-bounds/paid-beta/05-PAID-ORDER-TWELVE.md) raises the floor to 18, matching characteristic zero. At order 14, a [separate paid argument](lower-bounds/paid-beta/04-PAID-ORDER-FOURTEEN.md) raises the floor further to 21, matching characteristic zero. A [finite paid-field argument](lower-bounds/paid-beta/03-PAID-ORDER-EIGHTEEN-NINETEEN.md) gives 27 and 29 stages at orders 18 and 19, two more than the earlier arbitrary-ring bounds. [Its doubling extension](lower-bounds/paid-beta/02-PAID-DOUBLING-SURPLUS.md) raises order 20 from 28 to 30. These are mathematical proofs over all nonzero commutative unital rings using the denominator-cleared order equations; the ordered-field and characteristic-zero columns do not change.

## Improved DIRK lower bounds over arbitrary rings

The [paid grade-six proof](lower-bounds/paid-beta/DIRK-PAID-GRADE-SIX.md) raises the uniform arbitrary-ring floor by one for every order p≥12, to p + floor((p−1)/2) − 2. At orders 12 and 13 it gives 15 and 17, matching the characteristic-zero lower bounds. No diagonal sign, positivity or nonzero-diagonal restriction is imposed. At order 14, [a sharper proof](lower-bounds/paid-beta/DIRK-PAID-ORDER-FOURTEEN.md) raises the arbitrary-ring floor from 18 to 19. It uses stage chronology and the two paid ERK norms, bypassing the fixed reverse determinant. At orders 18 and 19, [a paid version of the grade-nine proof](lower-bounds/paid-beta/DIRK-PAID-ORDERS-EIGHTEEN-NINETEEN.md) raises the arbitrary-ring bounds to 25 and 27, matching characteristic zero. At order 20, [a flat-band and chronology argument](lower-bounds/paid-beta/DIRK-PAID-ORDER-TWENTY.md) raises the arbitrary-ring floor from 27 to 28. The characteristic-zero and ordered-field floor remains 29. The stronger paid floors have not yet been checked in Lean.

## Exact explicit minima over nonzero commutative rings

- [Order five](research/erk-five-ring-witness/README.md): six stages are necessary and sufficient if 120 is a unit. Otherwise no stage count attains order five.
- [Order six](research/erk-six-ring-minimum/README.md): seven stages are necessary and sufficient if 720 is a unit. A single rational tableau specializes to every such ring, including positive characteristic. This supersedes the eight-stage construction as a minimum, not as a denominator-removal technique.

- [Order seven](research/erk-seven-ring-witness/README.md): order seven is possible exactly when 5040 is a unit. The uniform stage count is between nine and ten; the ten-stage tableau reuses a Shanks endpoint to remove an extra denominator. The nine-stage universal question is open in this project.

- [Order eight](research/erk-eight-ring-witness/README.md): exact order eight is possible exactly when 40320 is a unit. The uniform thirteen-stage upper comes from splitting the final row of Shanks’s twelve-stage method to remove 41. This is an upper bound, not a minimum.

- [Order nine](research/erk-nine-moment-splice/README.md): exact order in 16 physical stages whenever 9! is a unit, improving the previous universal 21-stage upper.

- [Order ten](research/erk-ten-moment-splice/README.md): exact order in 21 physical stages whenever 10! is a unit, improving the previous universal 26-stage upper.

- [Orders eleven through twenty](research/erk-signed-reverse/README.md): exact explicit upper bounds **25, 28, 33, 37, 44, 50, 57, 64, 71, and 79 stages**, respectively, with coefficients in any nonzero commutative ring in which the corresponding factorial is a unit. Signed copies cancel the reverse donor error without dividing by a quadrature weight. Order eleven uses a [sharp eight-row reverse chart](research/erk-signed-reverse/SHARP-PAID-ERK-GRADE-FIVE.md); the [shorter scalar grids](research/erk-signed-reverse/SHORT-SYMMETRIC-GRIDS.md) use next-order defects instead of prescribing an extra moment.

The stated factorial unit is necessary for existence at any stage count. Literal arithmetic replays check all 3,047, 7,813, 20,299, and 53,272 rooted conditions at orders eleven through fourteen. At orders fifteen to twenty the general symbolic argument proves every rooted condition, and the literal tableaux have sample replays and exact next-order checks. None of these constructions is a new Lean certificate.

## Raising order while keeping the old stages

The [Newton-tail construction](research/newton-tail-order-raising/NEWTON-TAIL.md) raises order p−1 to at least p without changing the old stage equations, provided the output weights can be reassigned. It uses at most 2p new stages over nonzero commutative rings with p! invertible. Over the real algebraic numbers the [sharp worst-case costs](research/newton-tail-order-raising/SHARP-EXTENSION-COST.md) are floor(p/2) new ERK stages and ceil(p/2) for DIRK and SDIRK, with preservation of the SDIRK diagonal. For comparison, [fixing the old output weights](research/newton-tail-order-raising/FIXED-OUTPUT-LOWER.md) can force exponentially many new stages along a sequence of orders; some order-18 bases need at least 77 appended stages to reach order 19. These are extension costs, not absolute stage minima or Lean certificates.

## Rational strict SDIRK upper bounds at orders 8–20

The [two-order Newton construction](research/rational-sdirk-two-order/TWO-ORDER-NEWTON-TAIL.md) gives exact rational strict SDIRK in 13, 19, and 21 physical stages at orders 8, 9, and 10, respectively. These improve the earlier rational witnesses of 15, 23, and 27 stages. All rooted equations and next-bush failures were checked with exact rational arithmetic on the [literal tableaux](research/rational-sdirk-two-order/README.md).

At orders 11 through 20, an independently audited [extension using existing output stages](research/rational-sdirk-two-order/higher-orders/FAMILIES-AND-COUNTS.md) gives exact rational strict SDIRK in 28, 29, 37, 39, 48, 50, 60, 63, 74, and 77 stages, respectively. [The frontier argument](research/rational-sdirk-two-order/higher-orders/HEAD-PREPARATION-AND-FRONTIER.md) and [the rational quadrature choices](research/rational-sdirk-two-order/higher-orders/RATIONAL-GATES.md) prove these as symbolic recipes; no expanded higher-order tableau replay or Lean verification is claimed. These rational results do not change the real-algebraic table or Lean coverage.

## General mechanisms for changing or bounding stage counts

- [An iterable explicit two-order lift over factorial-unit rings](research/paid-affine-erk-two-order/AFFINE-TWO-ORDER-LIFT.md): from a prepared order-q seed, add n+2 physical rows for exact order p=q+2, with n=p if p is odd and n=p−1 if p is even. The exactness test does not require p+1 to be a unit. Both the hypotheses on the existing rows and the separate preparation costs are part of the theorem.
- [When old output stages pay a new moment](research/output-frontier-transfer/OUTPUT-SAMPLE-FRONTIER.md): an exact Legendre criterion detects which old clock samples substitute for another moment in the higher-order construction. See the [conditional stage savings](research/output-frontier-transfer/PHYSICAL-COUNT-TRANSFER.md) and the [comparison across ERK, DIRK and SDIRK](research/output-frontier-transfer/ERK-DIRK-TRANSFER.md). In particular, varying-diagonal DIRK can add two orders using only ceil(p/2) new real-algebraic rows when old output weights may be reassigned.
- [Reverse defect flags with one surplus dimension](research/one-surplus-reverse-flags/ONE-SURPLUS-CHARACTERS.md): under the stated head-rank and support hypotheses, a surviving surplus can be compensated by one clock factor or one extra degree of test budget. [Chronological rank tests](research/one-surplus-reverse-flags/PAID-HERMITE-EXIT-WITH-PREFIX-LEAKAGE.md) and [when they hide ordinary defects](research/one-surplus-reverse-flags/HIDING-ONE-SURPLUS-MARKED-QUOTIENT.md) require the actual prefix and marking hypotheses.

- [Preparing the next explicit lift with primitive observations](research/paid-affine-erk-two-order/PRIMITIVE-OBSERVERS.md): existing pure stages and moment observations can replace some new rows. Preparation and the final order lift are counted separately. The [archived 33-stage order-twelve tableau](research/erk-eleven-twelve-moment-splice/ARCHIVED-GRADE-TEN-OBSTRUCTION.md) cannot supply the grade-ten decoder for one proposed order-fourteen lift, even over the rationals; this does not rule out other seeds.
- [Physical clock tests for finite reverse characters](research/one-surplus-reverse-flags/FINITE-CHARACTERS-AND-LITERAL-DIAGONALS.md): with the stated prefix matching and visibility, the commutator detects a literal zero diagonal over a field. [Repeated clocks](research/one-surplus-reverse-flags/REPEATED-FIBRES-AND-NONZERO-DIAGONAL-OBSTRUCTION.md) and nonreduced coefficient rings require separate checks.
- [Output-clock grouping and chronology](research/output-clock-causality/GROUP-DEFECTS-AND-CAUSALITY.md): an exact group can give a smaller method of lower order. [The zero-mass construction](research/output-clock-causality/SILENT-CLOCK-SHARPNESS.md) shows why contributing clocks alone do not control local order. [The sign bound](research/output-clock-causality/SIGNS-AND-EARLY-OUTPUT.md) limits early active clocks in terms of negative weights.
- [Compensated DIRK prefix cuts](research/dirk-compensated-prefix-cuts/COMPENSATED-PREFIX-CUTS.md): two actual zero-through observations can impose a polynomial degree obstruction without assuming either pivot diagonal is zero. The profile count is distinct from the rank on physical rows.

- [Deleting stages while preserving specified rooted evaluations](research/stage-elimination/SAFE-CHRONOLOGICAL-ELIMINATION.md): chronological reduction preserves the diagonal class. [The named-row test](research/stage-elimination/NAMED-ROW-REBUILD.md) permits replacement reads from later retained stages when they still precede the actual consumer. Over rings, extending a descended output functional requires an additional check.
- [Successive physical marks](research/paid-successive-marks/SUCCESSIVE-MARKS-AND-SUPPORT.md): actual chronological observations bound a polynomial carrier and constrain the rank on physical clock fibres. [The zero-through variant](research/paid-successive-marks/STRICT-ZERO-THROUGH-MARKS.md) trades one degree for avoiding a zero-diagonal assumption.
- [Terminal tests at the actual last clock](research/moving-terminal-tests/MOVING-TERMINAL.md): an order identity detects when a true numerical null direction would force the last clock to be one, without assuming endpoint purity in advance.
- [Sharing physical correction rows across clock groups](research/sdirk-shared-physical-pivots/SHARED-PHYSICAL-PIVOTS.md): the same lower-triangular suffix can pay several groups’ order conditions. The exact [two-clock example](research/sdirk-shared-physical-pivots/TWO-CLOCK-FOUR-EXCESS.md) saves a row against the earlier construction with fixed co-site corrections, not against the unrestricted table.

These structural results have independent source audits. They do not change the unrestricted numerical tables or add Lean certificates.

## Further tests for row and clock reuse

- [Prime-local limits on rational quadrature grids](research/paid-quadrature-prime-test/PRIME-LOCAL-SITE-BOUND.md): a prime absent from the node denominators gives a scalar site-count obstruction. The exact enumeration also excludes small centered symmetric grids for orders 15 and 16.
- [Weighted first-consumption tests](research/weighted-first-consumption/ANTICHAIN-AND-EXACT-GRAM.md): at the first order where two altered branches can meet, the actual weighted Gram matrix determines whether the specified chronological restoration preserves order. [The support inequality](research/weighted-first-consumption/TERMINAL-SUPPORT-INEQUALITY.md) applies to stage-minimal tableaux under its stated visibility hypotheses.
- [Physical whole-fibre transfer](research/dirk-whole-fibre-transfer/PAID-FIBRE-TRANSFER.md): actual indicator membership and late contributing clocks can force extra stages in all three diagonal classes. These are conditional class bounds, not assertions about all minimal tableaux.
- [Endpoint corrections for strict SDIRK](research/sdirk-endpoint-echo/TWO-ORDER-ENDPOINT-ECHO.md): with the specified partial rooted-order profile, a few stages can supply the remaining corrections without changing the common diagonal or scalar moments. This does not raise an arbitrary seed or improve the unrestricted table.

## Bounds for particular stage architectures

- [Uniform explicit leapfrog paths](research/erk-uniform-leapfrog/UNIFORM-LEAPFROG-WIDTH.md): through order p, exactly 1 + floor(p²/4) physical stages are necessary and sufficient over any nonzero commutative ring in which p! is a unit. The lower bound allows signed weights on intermediate evaluations and sharing of identical stages. The construction gives 21 stages at order nine over ℤ[1/210]. This is a minimum within the stated architecture and an upper bound for unrestricted ERK over those rings, not an unrestricted lower bound or a Lean certificate.

- [First zero diagonal with a one-dimensional commutator kernel](lower-bounds/first-zero-corank-one-floor.md): at order 20, at least 51 stages, compared with 46 from the one-zero mask alone. The hypothesis is automatic for a zero first diagonal followed by nonzero diagonals, which need not be equal. The proof works over any field that admits the stated order and transfers to rings when the rank is witnessed in a residue field.
- [Fixed seven-stage ERK6 prefix](research/erk-six-ring-minimum/SEQUENTIAL-SUFFIX.md): retaining its seven literal rows requires at least 10, 11, and 13 physical stages at orders 7, 8, and 9. A parallel suffix cannot raise the order at any width. These bounds concern the fixed prefix, not all explicit tableaux.

Neither result changes the unrestricted tables or adds a Lean certificate.

## Sharp bounds for polynomial stage readouts

- [Exact dense derivative readout](research/sdirk-nonhomogeneous-kernels/DENSE-POLYNOMIAL-DONOR-MINIMUM.md): recovering all rooted stage-derivative polynomials through order q from one linear readout requires floor((q+1)²/4) stages if all the diagonal entries are nonzero. A common-diagonal Laguerre construction achieves equality over a suitable real algebraic field. The lower bound also covers varying nonzero diagonals, and finite sets of readouts obey a rank-dependent version.
- [Exact dense readout with a live explicit origin](research/sdirk-nonhomogeneous-kernels/LIVE-ORIGIN-DENSE-DECODER.md): when only the first diagonal is zero, the sharp real stage count is 1 + floor(q²/4), or 101 rather than 110 at q=20. The [lower proof](research/sdirk-nonhomogeneous-kernels/DENSE-SINGULAR-COMMUTATOR-FLOOR.md) allows varying nonzero later diagonals; the construction attains it with any prescribed nonzero common later diagonal. This is dense derivative accuracy, not ordinary endpoint order.
- [Sharp bound with a prescribed error band](research/sdirk-nonhomogeneous-kernels/PAID-DONOR-BAND-MINIMUM.md): prescribing only the Laguerre band through a larger cap, not the actual rows or error coefficients, also has an exact minimum. This shows why changing the depth alone does not shorten a preparation block with the same error band.
- [Use in a terminal construction](research/sdirk-nonhomogeneous-kernels/LOW-CUT-RANK-LANE-AND-PAID-PATH-PROFILE.md): a triangular shear gives 46 stages of ordinary order at least 14 and scalar and clock orders at least 21. Full ordinary order 20 remains excluded in that retained preparation at sufficiently small positive diagonal.

These are exact statements about specified readouts or preparations, not ordinary fixed-output stage minima or new Lean coverage.

## Rational contributing quadrature support

Separate from the stage tables, the [four-shift proof](research/rational-quadrature-four-shift/proof.md) gives at least \(\min(17,p-3)\) distinct contributing rational sites for quadrature order \(p\ge4\): 16 at order 19 and 17 at order 20. Weights may be arbitrary in a characteristic-zero field. Repeat sites are grouped first, and only nonzero aggregate weights count. The result transfers to Runge–Kutta by the reviewed bushy moments. It has an exact arithmetic check, not a new Lean certificate.

A [standalone 19-site rational rule](research/rational-quadrature-four-shift/standalone-19.md) attains quadrature order 20 with positive weights. This is not a Runge–Kutta stage upper bound. The [support index](research/rational-quadrature-four-shift/README.md) retains the stronger earlier low-order bounds.

The [donor realization theorem](research/quadrature-donor-realization/realization.md) goes in the other direction: every scalar rule of order at least \(p\) lifts to ERK, DIRK, or strict SDIRK with a prescribed common diagonal, preserving its contributing sites and weights. The same \(u/128\) rule gives tableaux of exact order 20 with 19 contributing sites and 209 physical rows, including 190 zero-output helpers. This equates the minimal contributing support with the scalar minimum, not the minimum stage count. No stage bound or Lean coverage count changes.

A separate [radii/33 prescribed-support realization](research/rational-support-radii33-splice/realization.md) keeps another 19-site rational rule's positive aggregate weights and has exact order 20 in 101 physical rows for ERK and 117 for strict SDIRK with common diagonal \(1/66\). This is not the \(u/128\) rule. The counts do not change the global stage tables; the proof and deterministic replay add no Lean coverage claim.

The [ordered-root geometry](research/rational-root-chart-geometry/ordered-root-geometry.md) gives a structural obstruction, not a support exclusion: with two or three paid nodal shifts the positive-dimensional smooth root charts have no dominant rational parametrization. A generic fixed prefix leaving one free root beyond Hankel completion gives a genus-one or genus-13 curve, respectively. The geometry alone does not decide attainability. It does not change a stage bound or Lean coverage.

The [two-shift elliptic criterion](research/two-shift-elliptic-transfer/elliptic-transfer.md) tests fixed-prefix completions exactly. A same-gap lower rule of exact order supplies rational infinity points and a conditional rank-free candidate. Neither of the known 19-site order-20 rules supplies the needed order-19 seed.

The [fixed-functional same-gap ladder](research/same-gap-seed-ladder/seed-ladder.md) shows that a genuine rational two-shift seed with a nontorsion completion pair can raise exact order and support repeatedly without changing the moments. The [uniform seed below](research/uniform-same-gap-seed/uniform-seed.md) meets that hypothesis.

## Lean certificate coverage

Lean and Mathlib v4.36.0 check 40 of the 60 strongest arbitrary-ring lower bounds, all 60 strongest characteristic-zero field entries, and 56 of the 60 strongest ordered-field and real entries. The previous uniform ring theorems remain checked, but do not reach the newly raised ERK floors at orders 10–20 or the new DIRK floors at orders 12–20. The characteristic-zero count includes the ERK exclusions at orders 12, 14 and 16–19, and the characteristic-zero DIRK exclusions at orders 14 and 16–20. An entry is counted only if the checked theorem reaches the current established numerical endpoint, not merely a weaker lower bound.

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
