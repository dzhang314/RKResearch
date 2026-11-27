# Lean checks for the real strict SDIRK13 forward research

The formal results in this package are:

- `RKResearch.Certified.FiveLadderThirteen.no_seven_site_ladder`:
  seven physical scalar nodes at the specified five reflected Newton
  ladder nodes and two extra sites cannot integrate through degree 12
  in any characteristic-zero field. Neither sign nor distinctness is
  assumed. The proof expands the actual weighted hull as moments,
  derives two vanishing Hankel minors and proves the exact integer
  Bézout identity using `ring`.
- `RKResearch.Certified.TwoDonorDense.paid_append_pure`: a genuine
  predecessor row for one paid shifted jet gives the next individually
  exact physical stage using the same diagonal. No full decoder for
  the old matrix is assumed.
- `RKResearch.Certified.TwoDonorDense.residual_row_payment`: agreement
  on the actual residual image gives agreement on every represented
  rooted-profile residual.

Lean 4.36.0 with matching Mathlib passed the source and typed audit
with only `propext`, `Classical.choice`, and `Quot.sound`. The
[separate research proof](../../../research/real-sdirk13-forward-ports/README.md)
covers the algebraic coordinate existence, instantiated two-port
bank and restricted 21-old-stage count. Those are not claimed as
additional Lean theorems here.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/five-ladder-thirteen-20261127/sources.sha256
lake build RKCert.ReviewedNative.FiveLadderThirteen RKCert.ReviewedNative.PaidStageAppend
lake env lean -j1 evidence/five-ladder-thirteen-20261127/AuditFront13.lean
```

The scalar source is reproducible by running
`gen_ladder_gate.py` in a scratch directory with SymPy and concatenating
its `gate_head.lean` with the archived `gate_body.lean`.
There is no oracle or additional axiom in either compiled module.
