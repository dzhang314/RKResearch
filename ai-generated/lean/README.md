# Runge–Kutta certificates in Lean

**General Q-type equivalence.** Write `c=A1`, let `Φ(t)` be the stage-weight vector and let `γ(t)` be the tree factorial. Over a characteristic-zero field, define the stage residual `Q(t)=AΦ(t)−c^|t|/γ(t)`, with componentwise powers. The central theorem, [`hasTreeOrderAtLeast_iff_rootCutTests`](RKCert/RootCuts.lean), proves that full order through `p` is equivalent to both:
 
- `(k+1) b·c^k = 1` for every `k+1≤p`, including the constant moment when `p≥1`;
- `b·(Q(t) ⊙ Φ(u))=0` for every nonleaf branch `t` and arbitrary rooted tree `u` with `|t|+|u|≤p`.

No triangularity, stage order, or sign assumption enters. Replacing the branch `t` by `|t|` leaves changes the normalized output error by exactly `γ(attach t u) b·(Q(t) ⊙ Φ(u))`. Repeated cuts end at the bush of the same order. This is a formalization of rooted-tree order conditions, not a new stage-count bound.

[An equivalent product formulation](RKCert/ResidualProducts.lean) replaces the second bullet by `b·(c^k ⊙ Q(t₁) ⊙ ⋯ ⊙ Q(tₘ))=0` for every nonempty list (repetitions allowed) satisfying `1+k+Σ|tᵢ|≤p`. No empty residual product is tested for zero; its conditions are the separate moments.

[An eight-stage rational negative control](RKCert/RootCutRegression.lean) passes every order-five moment and every test against `Φ(u)=c^k` using just **one** residual. Yet `b·Q(chain 1)^2=1/8` for the two-vertex branch. The tree with two such branches has weight `7/40` rather than `1/20`. Thus the unrestricted partner in the first formulation, or multiple residuals in the second, matters.

**Exact coefficient rings.** [`ScaledRootCuts.lean`](RKCert/ScaledRootCuts.lean) proves a division-free version of the first equivalence over *every commutative semiring*. The cut test is `γ(t) weight(attach t u) = weight(addLeaves |t| u)`. In any commutative ring this is exactly the vanishing of the paired **scaled** residual `γ(t) AΦ(t) − c^|t|`, even with zero divisors. No factorial is canceled without an inverse: necessity uses the exact weight of the bush-replaced tree as the inverse of its factorial. At fixed order `p`, the chain implies that `p!` is a unit, and Lean proves this unit condition is equivalent to invertibility of every tree factorial of order at most `p`. It does not assert existence of a tableau whenever `p!` is a unit. The unscaled product theorem above remains stated over characteristic-zero fields.

**Research certificate.** A concrete seven-stage rational diagonally implicit tableau satisfies every rooted-tree condition through order seven. Its eight-vertex bush has weight `167931/1344560` instead of `1/8`, so its algebraic order is exactly seven. The source gives the actual coefficients, not just the generation recipe.

**General theorem.** If a strictly lower-triangular `s`-stage tableau satisfies every rooted-tree order condition through `p`, then `p ≤ s`. For the classical four-stage rational tableau, Lean also proves that every condition through order four holds, and that order five is impossible.

These are exact, algebraic statements about the Butcher coefficients. They are not analytic theorems about convergence for differential equations, and they do not establish any of the stronger research lower bounds in the surrounding archive.

## What Lean checks

| File | Result |
| --- | --- |
| [`RKCert/RationalDIRK7.lean`](RKCert/RationalDIRK7.lean) | Verifies the variable-diagonal seven-stage tableau on `(0,3,4,8,10,13,14)/14`, its row sums, all order-seven identities, and a specific order-eight failure. This is the zero-central-parameter instance in the [rational DIRK construction](../upper-bounds/rational/dirk_rational_seventh_order_endpoint_christoffel_seed_and_true_nonlinear_shared_pole_20261123.md), not a proof of the whole family or stage optimality. |
| [`RKCert/Tree.lean`](RKCert/Tree.lean) | Defines rooted trees, their order and tree factorial `γ`, and elementary RK weights `Φ`. The chain with `n` edges has `n+1` vertices and factorial `(n+1)!`. |
| [`RKCert/Field.lean`](RKCert/Field.lean) | Over any characteristic-zero field, `γ(t) Φ(t) = 1` is equivalent to `Φ(t) = 1/γ(t)`. |
| [`RKCert/StageBound.lean`](RKCert/StageBound.lean) | `explicit_order_le_stages`: after `n` applications of `A`, the first `n` components vanish. For `n=s`, the chain condition would require `0=1`. The proof even works over any nontrivial commutative semiring for the denominator-cleared conditions. |
| [`RKCert/Enumeration.lean`](RKCert/Enumeration.lean) | An exact finite checker for a specified tableau; a theorem proves its list contains precisely all trees with at most `p` vertices. |
| [`RKCert/RK4.lean`](RKCert/RK4.lean) | Exact order four of the classical tableau over `ℚ`, using the complete tree checker and the general stage bound. |
| [`RKCert/Regression.lean`](RKCert/Regression.lean) | Negative control: a three-stage explicit tableau satisfies all chain tests through degree three but fails the two-leaf fork (`1/2` rather than `1/3`). |

`Tree.attach c r` adds `c` as a child of the root of `r`. This is an ordered representation: permuting siblings creates multiple representatives of the same unordered tree, not additional classical conditions. The weights multiply child factors in a commutative ring. The finite list through order four has nine ordered representatives (eight unordered trees); through order seven it has 197 (85 unordered trees). A chain has stage vector `Aⁿ 1`; this conclusion is derived from the same recursion as the branched cases. Stage indices in Lean are zero-based. The count includes the empty, zero-stage case.

## Reproduce

From this directory, with a Lean toolchain manager (`elan`) and Git installed:

```sh
lean --version                     # Lean 4.36.0
lake exe cache get Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.Nat.Factorial.Basic Mathlib.Data.Fintype.Basic Mathlib.Data.Fintype.Fin Mathlib.Algebra.Field.Rat Mathlib.Algebra.CharZero.Defs
lake build
lake env lean Audit.lean
```

The cache step only downloads Mathlib's compiled dependencies; it is optional if building them from source. `lean-toolchain` and `lake-manifest.json` pin the toolchain and dependency revisions. The project's only direct Lake dependency is Mathlib v4.36.0. The source contains no admitted proofs, user-supplied axioms, or native-evaluation proof shortcuts. `Audit.lean` prints the transitive axiom dependencies of the named certificates.

## Lower-bound certificates over commutative rings

[`RKCert/SDIRKStageFloor.lean`](RKCert/SDIRKStageFloor.lean) proves every current
ring-level strict SDIRK lower bound through order 20. The same bound applies
to a lower-triangular tableau with all diagonal entries units, even when the
entries differ. Over a field, nonzero diagonal entries suffice. The proof
counts independent stage vectors using the triangular matrix
`CA - AC - A²`; it does not assume signs, distinct nodes, or nonzero output
weights. It gives 55 at order 20. At order six this ring theorem gives 6. The separate characteristic-zero
exclusion below raises the floor to 7.

[`RKCert/DIRKSmall.lean`](RKCert/DIRKSmall.lean) proves the lower bounds 2, 3,
and 4 at orders 3, 4, and 5 for ordinary DIRK over every nontrivial commutative
ring. These theorems permit zero diagonals. The code uses the complete tree
conditions, not just the linear-test-equation conditions.

`lake build` checks both modules. `lake env lean Audit.lean` prints the axiom
dependencies and checks the order-20 field and order-10 zero-divisor ring
regressions.

[`RKCert/UniformERK.lean`](RKCert/UniformERK.lean) proves the uniform explicit
floor `max(p, ceil(3p/2) - 2)`. The proof treats odd orders without assuming that
the last stage has nonzero output weight.
[`RKCert/UniformDIRK.lean`](RKCert/UniformDIRK.lean) proves the uniform
unrestricted DIRK floor `p + floor((p-1)/2) - 3` for `p ≥ 6`. It combines
forward rank growth, the reverse triangular obstruction and a separate
terminal-stage argument. Both theorems apply to any nonzero commutative ring,
and both start from the full rooted-tree conditions. Their exact through-20
tables are checked in Lean. The stronger characteristic-zero and ordered-field
endpoints are a separate part of the formalization.

See [the Mathlib reuse audit](MATHLIB-REUSE.md) for standard-library interfaces and the RK-specific definitions we retain.


### The strict SDIRK order-six exclusion

[`RKCert/SDIRKOrderSix.lean`](RKCert/SDIRKOrderSix.lean) proves that a
strict SDIRK method of order six has at least seven stages over every
characteristic-zero field. In a hypothetical six-stage tableau, the rank
bounds force the forward and reverse spaces to have their smallest possible
dimensions. That yields constraints on the first and last stages. The proof
then splits according to whether the third stage depends on the second. In
each case, Lean checks explicit polynomial Bézout identities that contradict
the resulting equations. No external computer algebra is trusted by the proof.

[`RKCert/SDIRKOrderSixRing.lean`](RKCert/SDIRKOrderSixRing.lean) combines
this exclusion with the uniform commutator bound to certify all twenty
characteristic-zero strict SDIRK floors. It also proves the same result over
characteristic-zero commutative rings with a unit common diagonal. The bound
of seven is not asserted over arbitrary positive-characteristic rings.


## Characteristic-zero explicit Runge–Kutta lower bounds

## Checked results

`RKCert.Paired.grade_five_surplus` proves that a separated strictly explicit stage algebra has at least five independent pure defects at grade five. The next theorem, `RKCert.erk_stage_surplus_charZero`, derives separation from the actual denominator-cleared rooted-tree order hypotheses. For p ≥ 10, it proves

    s ≥ ceil(3p / 2) − 1.

It applies to every characteristic-zero commutative ring, including rings with zero divisors. There is no field ordering, distinctness, positivity or nonvanishing hypothesis on stage weights. Orders 10, 11 and 12 are exposed directly as at least 14, 16 and 17 stages, respectively. This is an existing lower bound formalized, not a sharpness claim. The stronger lower bound of 18 stages at order 12 is established on paper over characteristic-zero fields and ordered fields, but not by this Lean package. The separate all-characteristic uniform ERK theorem is available unchanged through `RKCert.UniformERKTable`.

## Proof map

* `ChronologicalCompression`: greedily retain independent chronological evaluation rows; reconstruct omitted inputs only from their own prefixes, and commute stage operations with restriction. The actual tree weights agree through the next grade.
* `StagePrimitives` and `ReceiverPrefix`: normalized tree defects imply literal algebraic polynomial primitive identities. A clean nonzero grade-five node gives a genuine order-five strictly explicit prefix after scalar normalization, not merely a matched quadrature rule.
* `NodeCompletion` and `ForwardAmplification`: use Mathlib's dot-product dual equivalence and Lagrange node projection to split annihilating rows by node. The earliest two chronological nonzero completions show that C-invariance forces at least two new ranks at the next grade, without an ambient basis assumption.
* `GradeFiveSpace`, `GradeFiveCaseOne` and `QuarticPrimitive`: if the quadratic defect and its clock image are independent, a minimal grade-five rank forces one polynomial chain. Five distinct predecessors then make a degree-four polynomial difference vanish. The resulting polynomial divisibility forces the quadratic head to be a monomial, which contradicts clean primitive evaluation at a nonzero node.
* `GradeFiveDependent`, `CaseIIScalars`, `CaseIIFiveRows` and `CaseIIStage`: the remaining minimal profile has a quadratic defect supported at the normalized second node and only one new clock chain. The first five physical rows, using their actual graded tree tests, then force a nonzero tap at a repeated node; the next clock word contradicts the pure span.
* `GradeFiveReduction`, `GradeFiveCount`, `ERKGradeFive`: assemble both cases, propagate the rank surplus, apply the paired forward/backward count with the odd correction, and transfer to every characteristic-zero commutative ring.

## Replay

Lean 4.36.0 (commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9), Lake 5.0.0-src+611c117 and Mathlib v4.36.0 (commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842). With the pinned Mathlib packages and normal dependency cache available:

    lake build
    lake env lean Audit.lean
    lake env leanchecker --verbose RKCert.ERKGradeFive

`Audit.lean` prints exact theorem types and axioms; it also elaborates exclusions at one stage below each promised order and a ring-with-zero-divisors test. Only standard Lean axioms are used. No admitted proof, custom axiom or native decision procedure is used.


## Logarithmic explicit stage bound

[`RKCert/ERKLogarithmic.lean`](RKCert/ERKLogarithmic.lean) proves
`s ≥ ceil(3p/2) − 1 + floor(log₂(floor(p/10)))` for order `p ≥ 10` over
characteristic-zero commutative rings. The additional ranks come from ruling
out an entire doubling interval of unit growth. The proof at order 20 gives
30, not the stronger ordered-field lower bound of 32.

[Appendix B](APPENDIX_B.md) contains the two exact scalar exclusions needed
for the 18-stage order-12 result. The full rank argument that supplies their
hypotheses is now checked and combined with those exclusions.

Run `lake env lean AuditERKField.lean` and `lake env lean AppendixBAudit.lean`
after building to reproduce the additional axiom audits.

The [DIRK grade-six proof](DIRK-GRADE6.md) also verifies the current
characteristic-zero lower bounds of 15 stages at order 12 and 17 at order 13.
It does not establish the stronger finite order-14 and order-15 endpoints.


## Order 12 and higher DIRK

- [Order-12 ERK proof](ORDER_TWELVE.md): at least 18 stages over all characteristic-zero fields and commutative rings. The [reverse argument](REVERSE_OBSTRUCTION.md) eliminates the earlier case split.
- [DIRK parity proof](DIRK-PARITY.md): general bounds at even and odd orders, reaching 23 at order 17 in characteristic zero.
- [Low-order ERK chart reductions](ERK-LOW8-9.md): necessary conditions for the order-eight and order-nine candidates, not full exclusions.

After `lake build`, run `lake env lean OrderTwelveAudit.lean`,
`lake env lean ReverseObstructionAudit.lean`, `lake env lean AuditDIRKParity.lean`,
and `lake env lean AuditLowERK.lean` to reproduce the additional axiom audits.

## Additional structural certificates

- [Order-eight ERK reductions](ERK-ORDER-EIGHT-REDUCTIONS.md): a ten-stage candidate over a characteristic-zero field has one or four distinct off abscissas.
- [Even-order DIRK boundary](DIRK-EVEN-BOUNDARY.md): physical terminal cardinal and fixed grid, mutual annihilator ranks, and the conditional order-sixteen quartic test.

These certificates support the remaining finite-order proofs; they do not change the stage-bound tables. After building, the corresponding replay entry points for the axiom audits are `AuditOrderEight.lean` and `AuditDIRKEven.lean`.

The [fixed-Lobatto factor theorem](LOBATTO-FACTOR-GATES.md) rules out a vanishing first moment for the small factors relevant at DIRK orders 14 and 16 over any characteristic-zero field. It uses exact prime-field checks and does not require real coefficients. Audit: `lake env lean AuditLobattoFactors.lean`.

- [Finite ERK midpoint](ERK-FINITE-MIDPOINT.md): common characteristic-zero rank and head structure for orders 16–19.
- [DIRK order 15](DIRK15-SUPPORT.md): an exhaustive three-way reduction of a hypothetical 20-stage characteristic-zero tableau and exact moment tests.
- [Nonlocal reverse DIRK](DIRK-NONLOCAL-PORTS.md): physical pivot equations and joint coordinatewise vanishing at order 16 in the nonlocal case.

These modules also supply structural prerequisites, not new numerical lower bounds.

- [Order-nine ERK Radau reductions](ERK-ORDER-NINE-RADAU.md): the five-on/five-off rank-nine case is impossible; the rank-ten scalar test is independent of the remaining physical extraction.
- [Fixed-Radau root certificates](RADAU-ROOT-CERTIFICATES.md): modular specialization for prescribed distinct roots and exclusion of seven off abscissas.
- [Local DIRK reverse obstruction](DIRK-LOCAL-REVERSE.md): removes the local-branch hypothesis from the even-order marked-port theorem without claiming a new numerical lower bound.

Audit with `lake env lean AuditOrderNineRadau.lean`, `lake env lean AuditRadauSevenOff.lean`, and `lake env lean AuditDIRKWeightedLocal.lean`.

## Four additional ERK endpoints and a general DIRK bound

- [ERK orders 16–19](FINITE-ERK16-19.md): characteristic-zero stage floors 24, 26, 27, and 29, each over fields and commutative rings.
- [Even DIRK orders 22 and above](DIRK-EVEN-FROM-22.md): at order 2m with m ≥ 11, the characteristic-zero stage floor improves from 3m−3 to 3m−2.
- [Six off nodes at ERK order nine](SIX-OFF-FIVE-ON.md): six on nodes are necessary in the twelve-stage analysis. This reduction does not change the order-nine stage floor.

Audit with `lake env lean FiniteERK16to19Audit.lean`, `lake env lean AuditDIRKEvenFifthFloor.lean`, and `lake env lean AuditSixOffFiveOn.lean`.

- [ERK order 14](ORDER-FOURTEEN.md): 21 stages over characteristic-zero fields and commutative rings, without ordering.
- [DIRK orders 18 and 20](DIRK-ORDER18-20.md): 25 stages at order 18 and a certified intermediate lower bound of 28 at order 20, over characteristic-zero fields and commutative rings.
