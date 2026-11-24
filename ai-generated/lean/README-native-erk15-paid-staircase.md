# Native order-fifteen marked staircase through grade twelve

The ordinary reviewed assumptions (strict lower triangularity,
`RKResearch.HasOrder A b 15`, at most 22 stages and a characteristic-
zero field) now give a physical marked one-head chart from either
first-escape entrance through grade twelve.

* In the reusable `MarkedReverseDebit` module, when the marked forward
  space reaches capacity, its true annihilator equals the all-monomial
  flag. The terminal mark is accounted for by the same physical
  zero-tail condition, not by counting an extra first seed. If the
  forward space is clock invariant, its annihilator is invariant under
  the reflected clock. The proof then calls the single checked
  `ReverseClockGain.reverse_clock_invariant_gain` algorithm (declaration
  namespace `RKResearch.Certified.Graded.Reverse`).
* For a full marked grade j at order fifteen, invariance costs
  floor((15−j)/2) against the preceding physical grade. At j=7 the
  checked debit is specifically four new dimensions, but grades 6
  and 7 differ by only two. At already paid grades j=8,9,10,11 the
  preceding jump is one and the debit is at least two. Hence each
  clock step grows and reaches the next exact cap.
* `order15_physical_staircase` retains the actual same mesh and head.
  With the first escape at grade a+1 (a=6 in the marked alias case,
  otherwise a=7), the grade-j space equals the degree-a coefficient
  band plus the physical head chain of length r+3+j−(a+1), for all
  a+1≤j≤12. `order15_marked_high_ranks` gives ranks j+8+d uniformly
  for 8≤j≤12, in particular 20+d at grade twelve.

The existing Jacobi packet accompanies the same actual polynomial with
no additional premise or arithmetic. No mesh gate, large-r exclusion,
or 23-stage proof is claimed here. The existing first-escape seal is
untouched; both proofs use the reviewed tree type, weights, and order
conditions directly and do not import any legacy tree/order bridge.

## Verification

Two additive modules and one independent chart-and-moments consumer,
compiled with Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`),
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and human reviewed
sources at `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. Both new modules
also passed leanchecker replay. All 13 declaration audits report
only propext, Classical.choice and Quot.sound. The transitive local
source manifest pins the shared `ReverseClockGain` and checks every
overlap against the unchanged prior first-escape seal
`37a1542f5fd71538b8b7ad52fbad95026daffeb09af4acfb762944cce6f62b0b`.
No network, push, human-source edit, or arithmetic replay was used.
