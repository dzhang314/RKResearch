# Native ordered ERK9: only exactly five defective clocks remain

For a strictly lower twelve-stage tableau over any ordered field, the original
reviewed `RKResearch.HasOrder 9 A b` forces exactly five distinct quadratic
defect clocks and either five or six distinct clean clocks. In particular,
**13 ≤ s whenever the number of distinct defective clocks is not five**.

The theorems are `RKResearch.Certified.Graded.MultiOff.order9_exactly_five_off`
and `explicit_order_nine_off_count_ne_five_at_least_thirteen`. Syntactically
the inputs are only the original matrix, output row, strict explicitness, and
reviewed order. No positivity, bounded nodes, distinct rows, regularity, or
separate rank assumptions are imposed.

## Proof and remaining gap
* Eight or more defective clocks would force exactly eight off and four clean
  with a nonvanishing degree-one/two common head on the clean knots. Native
  terminal rank, the first physically available clean row, and the exact
  cubic/quartic scalar Lobatto gates rule this out.
* For five clean nodes, the original weighted tree probes give the anchored
  Radau hull. Its degree-two head does not divide that hull. Two adjacent
  interpolation columns therefore recover the full state space for six or
  seven off knots. The paid native adjoint marks the physical terminal
  coordinate; it would be clean at one, impossible for the five-clean rule.
* Six off/six clean similarly forces a pencil divisor with a vanishing
  primitive on a complementary root, contradicted by the checked scalar
  pencil gate.
* Remaining physical branches: (5 off, 5 clean), (5 off, 6 clean). The latter
  still needs its **native physical** K8/terminal-product construction before
  applying the already checked scalar `six_on_witness_impossible`.
  No unconditional thirteen-stage bound is asserted here.

## Reproduction

Additive dependency: sealed native multi-low source packet
`a69e1eb2b7ca05594d5075eb03e552ebd3804d8fbe37bc7b223a07073584bf9d`.
Unchanged reviewed basis: `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
Pinned Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) and
Mathlib v4.36.0 (fc4f59e577feb1a4956671bc04ac18aaaf8cd842).
Compile the following six modules individually in this order, then run
AuditReviewedNativeOrderNineMultiHigh.lean: OrderNineMultiHighHead,
OrderNineMultiHighTerminal, OrderNineMultiHighExclusion, OrderNineMultiCleanRadau,
OrderNineMultiFiveClean, OrderNineMultiSix. Only cached scalar arithmetic
certificates, not legacy tableau/order theorems, are consumed. No large
residue rows, scalar arithmetic packages, or earlier leaves were replayed.
