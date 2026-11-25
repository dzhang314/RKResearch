# Hidden clock columns: checked affine identity and moment ladder

The native theorem is
`RKResearch.HasOrder.hiddenClock_ladder_iff`. It uses the actual
reviewed [`HasOrder p A b`](../../../../RKResearch/OrderConditions.lean),
not a separate scalar or transposed tableau order. Let `T` be a nonempty
finite cover of the nonzero aggregate output masses, `S ⊆ T` the stops
being compared, and `H` a finite certificate for the actual nonzero
hidden grouped columns against a polynomial profile `F`. For
`F.natDegree ≤ d` and `d + T.card + 1 ≤ p`, the theorem checks

```text
(∀ a ∈ S, N_F(a) = B(a) * I_{a,1}F)
  ↔ the first p − d − T.card − 1 + S.card moments of
    x ↦ N_F(x) * (nodalHull (T \ S)).eval x on H are zero.
```

This is the full finite equivalence, not just detection on one chosen
stop. If `H.card` is at most that count, those zero moments force all
hidden grouped columns against `F` to vanish. The exact set of nonzero
hidden clock values is also defined from the tableau. The real ERK and
DIRK clients below use this bound to remove leakage before concluding a
true reflected local integral is zero. They still require physical
strict-column cancellation and nonzero aggregate output at the stop;
the DIRK client also requires a true reflected stop root. Neither
client erases an independent signed atom or establishes a stage bound.

## Checked sources and endpoints

| Lean library | Checked scope | Checked audit |
| --- | --- | --- |
| [`ClockSuffixRowFunctional`](../../RKCert/ReviewedNative/ClockSuffixRowFunctional.lean) | The actual weighted column test for polynomial source and receiver arguments under the mixed degree guard `deg Q + deg F + 2 ≤ p`; no triangularity needed. | [Affine audit](../../AuditHiddenClockLeakageClients.lean) |
| [`HiddenClockLeakage`](../../RKCert/ReviewedNative/HiddenClockLeakage.lean) | The exact affine hidden-leakage identity, reflected interval, and real triangular client types; the unaccounted hidden term is retained unless paid or zero. | [Source](../../AuditHiddenClockLeakageClients.lean), [exact output](affine.audit-output.txt) |
| [`FiniteClockMomentLadder`](../../RKCert/ReviewedNative/FiniteClockMomentLadder.lean) | Monomial detection, complementary-hull equivalence, and invariance under paid selectors with the same visible values. Only a field is needed, with no `HasOrder` or characteristic assumption. | [Silent literal-sum audit](../../AuditFiniteClockMomentLadder.lean) |
| [`HiddenClockMomentLadder`](../../RKCert/ReviewedNative/HiddenClockMomentLadder.lean) | Actual grouped order-law specialization, low-support zero, and independent real ERK/DIRK client types. | [Source](../../AuditHiddenClockMomentLadder.lean), [exact output](ladder.audit-output.txt) |

The separate [mathematical ladder and sharpness proof](../../../research/causal-profile-reduction/hidden-clock-moment-ladder.md)
also derives sign variation and constructs an all-even-order sharpness
family. **Those results are not formalized in these modules.** The
[donor-leakage](../../../research/causal-profile-reduction/donor-suffix-leakage.md)
and [stopped-selector](../../../research/causal-profile-reduction/selector-paid-stopped-atoms.md)
notes are unchanged; the independent sign-law comparison remains a
separate mathematical premise.

## Replay evidence

The exact four library and three audit invocations all exited zero
under Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) and
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The record is in
logical dependency order, using compatible private object snapshots,
not a fresh single build at the archive revision. The two printed
outputs are unchanged; together they have sixteen named types and
seven axiom reports, each using only `propext`, `Classical.choice`, and
`Quot.sound`. The pure literal-sum audit passed silently. Nonfatal
linter warnings in library builds were not changed or suppressed.

- [Checked source input hashes](source-inputs.sha256)
- [Reviewed source and toolchain pins](reviewed-providers.sha256)
- [Observed invocation exits and exact log commitments](replay.tsv)
- [Verified private output fragment commitments](verified-object-fragments.tsv)

No compiled objects are included. Proof-only repairs in the two
measured modules are already in the exact source hashes above, not
separate patches. Check the manifests relative to the repository root.
For replay, with the pinned dependencies already available, start in
`ai-generated/lean`:

```sh
lake build +RKCert.ReviewedNative.HiddenClockMomentLadder
lake env lean -j1 -M1800 AuditHiddenClockLeakageClients.lean
lake env lean -j1 -M1800 AuditFiniteClockMomentLadder.lean
lake env lean -j1 -M1800 AuditHiddenClockMomentLadder.lean
```

These are reproduction commands, not claims that a new Lake build
was run for this archive. No default target or umbrella import changes.
