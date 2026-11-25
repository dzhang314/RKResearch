# ERK order eight: the one-off branch at ten physical stages

Import `RKCert.ERK8OneOffFin10`. The [native entry point](../../RKCert/ERK8OneOffFin10.lean)
is `RKResearch.Certified.Graded.OneOff.Eight.erk8_one_off_exclusion`.
It excludes a strictly lower tableau of width `Fin 10` over a
characteristic-zero field when the original reviewed
`RKResearch.HasOrder 8 A b` holds, its native order-eight midpoint
certificate `Reverse.ERKEvenHorizon A b 4` is supplied, and
`(OneOff.offKnots A).card = 1`. The “off” set counts distinct clocks
carrying the actual quadratic defect, not physical rows. The theorem
does not conflate physical rows sharing a clock.

This closes the **singleton-off branch only**. It is not the
four-off exclusion, an exhaustive-dispatch result, or an all-width
stage lower bound. This evidence does not change the stage table or
the strongest-endpoint coverage counts.

## Proof shape and exact audit

The proof derives the global normal form, separates the two defects and
earns the nine-column grade-five range from reviewed order. Causal
interpolation on the original rows then constrains the seventh physical
row. The actual grade-four terminal coordinate fixes the cubic, and its
equations force incompatible roots at the first clean clock and its
double. No external row profile, rank or cancellation callback is
assumed by the entry point.

The native body and the [separate typed audit](../../AuditERK8OneOffFin10.lean)
both exited zero under Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The audit produced no object
and elaborated two exact ordered-field clients. One applies the
contradiction. The other checks the original physical prefix and
grade-five rank and range as outputs, not assumptions. The
[unmodified raw audit output](typed-audit-output.txt) contains 21 named,
transitive reports, each listing only `propext`, `Classical.choice`
and `Quot.sound`; see also [the parsed sets](actual-axioms.tsv).

## Source and replay boundary

[Acceptance](acceptance.tsv) binds each of the nine added body sources
and the audit to its actual compiler exit and digest. The exact
[public prerequisite sources](reviewed-providers.sha256) and the
[added source bytes](added-sources.sha256) are separately pinned.
The two [shared support providers](reused-support.tsv) already match
the measured sources in the base; neither is republished or rebuilt
under a second module name by this overlay.

Three elaboration stops were repaired before the successful chain:
- Row 28 explicitly interprets the origin submodule result as a
  coordinate equality and supplies the already intended scalar 1 in
  the polynomial degree calculation.
- Row 29 normalizes two local polynomial aliases before applying the
  existing zero and subtraction simplifications.
- Row 33 applies the already checked Lobatto cubic degree lemma instead
  of redoing its coefficient simplification.

The [repair ledger](measured-repair-chain.tsv) binds the original
failed source/log digests, narrow repaired source digests and the
diagnostics with only their source path prefixes normalized. No
mathematical hypothesis or statement changed in these repairs.

The accepted execution was a serial replay with exact project inputs
and outputs coherently in one private project root, and an allowlisted
pinned external cache. This is not a separate cold package build.
For a later replay, use the pinned certificate package and compile the
body sources in the [acceptance order](acceptance.tsv) against their
listed prerequisites, then check the unchanged audit without object
output. No compiled objects or private execution paths are included
in this evidence.
