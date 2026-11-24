# Native reviewed tree and graded stage calculus

This is the shared native stage/residual spine for the ERK endpoint
proofs. It is not a façade over the old tree proof: every tree
generator is the human-reviewed `RKResearch.FiniteRootedTree`,
every actual stage column is `RKResearch.Φ`, and every assumption of
order is `RKResearch.HasOrder`. Neither the legacy tree modules nor
the reviewed-to-legacy order bridge were on the Lean path for the
native leaves or the consumer. The checked order-15 and lower-order
archives were left untouched.

The exact reviewed input is `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
All new public modules follow `RKCert.ReviewedNative.*`; mathematical
declarations live under `RKResearch.Certified.Graded`, with the
tree-root merge operation under `RKResearch.FiniteRootedTree`.
The shared native `RootMomentCuts` and `BushyMoments` are imported
by their unified names; their sources and the human sources are
not duplicated here.

## Scope and actual proof contracts

1. `GradedColumns` and `GradedDefects`: normalized real tree columns,
   their exact paid mixed probes, concrete `treeSpace` and same-order
   difference `zeroSpace`, graded clock/matrix actions, origin
   vanishing, and membership of the actual monomial stage defect.
   Positive-natural/tree coefficient units come from genuine
   reviewed order conditions rather than characteristic zero.
2. `GradedProducts` and `GradedPrimitives`: physical graded products
   and defect-ideal multiplication; actual polynomial evaluation,
   formal primitive, coefficients, derivative, grade advance, and
   native exact primitive residual. The polynomial primitive residual
   itself needs a characteristic-zero field but no output-weight
   hypotheses, so it applies after chronological compression.
3. `FiniteCauchy` and `GradedSeparation`: elementary finite moment
   injection by Mathlib's polynomial root-count with a common
   denominator; the exact polynomial-plus-defect span and
   `explicit_midpoint_rank_eq`. This includes the origin saving one
   moment at the even midpoint, over arbitrary actually attained
   fields.
4. `CausalStage` and `GradedGrowth`: causal operators in either
   chronology, the invariant-seed plateau, and actual forward
   grade rank/strict growth. The causal layer is the one-seed
   strictly triangular result; it does not supply the separate
   DIRK diagonal two-seed theorem or an odd/backward marked chart.
5. `GradedPrefix`: actual leading matrix and vector restriction,
   exact restriction of `Φ` and `zeroSpace`, and literal
   `HasOrder` of the rescaled leading tableau at a nonzero clean
   receiver. This is not only a scalar quadrature consequence.

The native proof uses Mathlib `Matrix.mulVecLin`,
`dotProductBilin`, `LinearMap.mul`, `Polynomial.lsum`,
`Matrix.submatrix`, and existing polynomial degree/evaluation
and subspace/rank APIs. The reviewed `Φ_bushyTree`, `order_bushyTree`,
and `forestFactorial_bushyTree` are used directly; no parallel
bushy or tall recursion is supplied.

## Verification

Only named scoped leaves and a consumer were compiled with
Lean 4.36.0 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The pinned checks can be repeated from `ai-generated/lean`:
`lake build RKCert.ReviewedNative.GradedGrowth RKCert.ReviewedNative.GradedPrefix`.
To run the axioms check, first compile `checks/GradedConsumerCheck.lean`
to `.lake/build/lib/lean/RKCert/ReviewedNative/GradedConsumerCheck.olean`
with `lake env lean -o`, then run `lake env lean checks/GradedAxioms.lean`.
Neither a broad package rebuild nor older-toolchain support is claimed. All fourteen axiom checks
are standard Lean only. This package establishes the reusable
direct native proof internals, not a recheck or replacement of the
whole p9 or p15 endpoint.
