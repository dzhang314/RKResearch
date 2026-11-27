# Fourteen-stage exact ERK order nine on seven contributing clocks

A new literal **14-stage explicit Runge–Kutta method of exact order nine**, over the real algebraic numbers, with seven abscissae of positive aggregate weight, scalar precision **nine** (all polynomial degrees 0–9), and only one repeated contributing high clock. This is a changed-mesh control, not a change to the unrestricted order-nine or order-ten stage tables. Its tenth tall condition fails.

The [exact cancellation proof](EXACT-PROOF.md) establishes the rooted equalities. The [directed replay](REPLAY.md), source and tableau fixture provide independently reproducible root isolation, positivity, strictness, and the next-order failure. Intervals enclosing zero are **not** proofs of order.

The contributing sites in increasing order are approximately
\[
 (0,\ .07117297253,\ .24729386317,\ .49458772635,\ .74311623316,\ .92353731031,\ 1).
\]
Their aggregate weights are all positive. Only the clock \(\xi=.49458772635\ldots\) receives two distinct nonzero-weight physical rows. Earlier prefix stages at the same clock remain zero-weight; no reverse weight inversion ever uses them.

## Native scope

The Lean modules ERK149SevenClockPrefix and ERK149SevenClockPayments respectively certify the actual anchored rational prefix tree sources and the seven-word reviewed nonlinear order bridge with the successive three chronological contractions. The generic native bridging lemmas and exact prefix checks were compiled on Lean/Mathlib 4.36.0. The independent Lean Core interval checker recomputes the endpoint signs and the simple cubic branch enclosures on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The scalar reverse payment and existence of the algebraic mesh use the mathematical proof and the replay, not one closed native theorem about the concrete algebraic witness.
