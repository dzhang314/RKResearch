# Reviewed order-twelve ordinary DIRK floor on non-C(2) tableaux

The Lean theorem
\[
  \texttt{RKResearch.Certified.Graded.Reverse.dirk_order12_nonC2_floor}
\]
works over an arbitrary field, without characteristic zero or
ordering assumptions. Its direct premises are literal lower
triangularity, reviewed \(\texttt{HasOrder}\ 12\), and nonzero
actual quadratic-defect vector \(2A\mathbf c-\mathbf c^2\).
Then the number of stages is at least fifteen. The required
small units are consequences of the rooted order hypothesis.

This is only the non-C(2) branch. It neither builds a real
optimum on its own nor replaces the separate arbitrary-ring
mathematical floor. A specialization that loses the quadratic
defect does not meet its hypotheses.

## Count

The reviewed forward grade-five lower gives at least four
actual defect directions because the quadratic one is nonzero.
The paid separation at grade five puts six scalar directions
beside these in the actual \(\texttt{treeSpace}\), giving at
least ten. The existing unanchored reverse room theorem pays
five further physical coordinates at order twelve, including
its actual endpoint refund. It needs \(5+5+2=12\) for both
checks and uses no order-thirteen equation.

The only source import is
\(\texttt{RKCert.ReviewedNative.DIRKTerminalRank}\).
The attached receipt is for Lean 4.36.0 and the matched
Mathlib version. It reports only the ordinary axioms
\(\texttt{propext}\), \(\texttt{Classical.choice}\), and
\(\texttt{Quot.sound}\). No cross-version Mathlib compile
is asserted for this module.
