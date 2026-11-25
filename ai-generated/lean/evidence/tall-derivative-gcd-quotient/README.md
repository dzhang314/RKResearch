# Finite tall response: the derivative-gcd degree bound

The checked result is
`RKResearch.Certified.TallFiniteResponse.Fraction.order_le_num_add_derivativeGcd`.
For a characteristic-zero field, the reviewed `HasOrder p A b`, and a
normalized finite tall fraction `Fraction A b P Q`, Lean proves

```text
p ≤ P.natDegree + (Q.natDegree − (gcd Q Q.derivative).natDegree).
```

The `Fraction` hypothesis is the ordinary polynomial cross equality
against the physical characteristic numerator and denominator, with
`Q.coeff 0 = 1`. The result applies to an unreduced pair as well as a
reduced one; using the actual reduced pair makes it cancellation-sensitive.
It needs no triangularity, sign, or ordering assumption. It is a
necessary **tall-only** restriction, not a new unrestricted stage minimum.

## Checked parts in dependency order

| Module | What is checked | Typed audit and recorded output |
| --- | --- | --- |
| [TallCharacteristicResponse](../../RKCert/ReviewedNative/TallCharacteristicResponse.lean) | Finite characteristic pair via Cayley–Hamilton; normalized cross equality and paid coefficients from the literal reviewed tall trees. The audit also checks that a coprime denominator splits when `A` is lower triangular. | [source](../../AuditTallCharacteristicFirstGate.lean), [output](F1.audit-output.txt) |
| [TallPoleMultiplierWindow](../../RKCert/ReviewedNative/TallPoleMultiplierWindow.lean) | A supplied multiplier `V*Q.derivative = B*Q` with its exact degree endpoints gives a backward zero-window step, no long consecutive zero block, and the finite degree bound. | [source](../../AuditTallPoleMultiplierWindow.lean), [output](W1.audit-output.txt) |
| [TallPoleMultiplierProducer](../../RKCert/ReviewedNative/TallPoleMultiplierProducer.lean) | Euclidean gcd gives the cofactors and their degrees. The audited endpoint uses `derivativeGcdQuotientDegree Q`, as in the displayed formula. | [source](../../AuditTallPoleMultiplierProducer.lean), [output](W2.audit-output.txt) |

The [mathematical distinct-pole proof](../../../research/tall-distinct-pole-recurrence/README.md)
also identifies this degree difference with the number of distinct
geometric roots and treats sharpness. **That identification and those
sharpness results are not formalized here.** The Lean theorem above is
the quotient-degree statement only. None of these modules transfers
nonlinear tree order to a reduced tableau.

## Replay evidence

The recorded source pair for each module and its audit passed in serial
under Lean 4.36.0 (commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`)
with Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The
[exit ledger](replay.tsv) records the six successful invocations. All
thirteen named axiom reports list only `propext`, `Classical.choice`,
and `Quot.sound`. The W1 audit's benign unused-simp warning has its
private absolute source prefix removed; the axiom output is unchanged.
The [checked inputs](source-inputs.sha256) and [reviewed providers](reviewed-providers.sha256)
are hashed relative to the repository root.

To replay using the pinned toolchain and dependencies, from
`ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.TallPoleMultiplierProducer
lake env lean -j1 -M1800 AuditTallCharacteristicFirstGate.lean
lake env lean -j1 -M1800 AuditTallPoleMultiplierWindow.lean
lake env lean -j1 -M1800 AuditTallPoleMultiplierProducer.lean
```

The explicit target builds the preceding two modules as dependencies.
No umbrella import or default build change is required. These commands
are a replay recipe, not evidence of a new build at the archive revision.
