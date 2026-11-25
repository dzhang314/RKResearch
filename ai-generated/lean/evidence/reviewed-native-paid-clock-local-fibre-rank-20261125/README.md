# Checked generic clock-local rank and exact fibre sum

These two independent generic Lean bodies and their separate typed audits were
measured with Lean 4.36.0. Each audit loaded its own previously measured body
and requested no object output. `result.json` records exact source, log and
artifact digests, actual exit statuses and the named stock-only axiom reports.

- `PaidClockLocalRank` preserves the clock-local part at every positive
  reverse grade of the measured staircase. Its dimension is at most the
  initial reverse dimension plus one, with equality precisely when the
  grade-one primitive reverse space is invariant under the actual stage
  clock. The two-height wrapper states its full payment and capacity
  hypotheses explicitly.
- `ClockLocalFiberRank` is independent of the staircase. For any finite
  stage set, field, clocks and column space, it identifies the clock-local
  annihilator with the product of the annihilators of the actual restricted
  column spaces. Its rank is the sum of the fibre deficits; equivalently,
  that rank plus the sum of the restricted-column ranks is the stage count.

The fibre-rank body retains its original measured private-helper linter
warning; no new diagnostic was admitted by the typed audit. No numerical
order-specific client, terminal step or stronger stage lower bound is claimed.
