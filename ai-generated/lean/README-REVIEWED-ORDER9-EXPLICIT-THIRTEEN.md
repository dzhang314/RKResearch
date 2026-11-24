# Ordered ERK order nine needs at least thirteen stages

Import `RKCert.ReviewedNative.OrderNineExplicitThirteen`. The endpoint is
`RKResearch.Certified.Graded.MultiOff.explicit_order_nine_at_least_thirteen`:

```lean
{K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
{A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
(ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder A b 9) : 13 ≤ s
```

No assumption about signs of coefficients, repeated abscissas, collisions
between clean and defective clocks, or a separately given rank profile
is needed. This is a lower bound for the reviewed rooted-tree conditions
over every ordered field. The physical proof uses the original matrix and
output row throughout; no alternate tableau/order conversion is present.

## Exact closure

The prior one-off and multi-off packets leave only a putative 12-stage tableau
with five distinct defective clocks and six distinct clean clocks.
On this last chart, the native grade-six space earns an actual two-row
contrast, whose transpose sees all ten nonterminal cohorts. The proof gathers
rows with the same **tag and clock** without dropping any physical stage, and
accounts for the genuine incoming-row difference. The native adjoint and
quadrature identities supply the physical affine equations, four distinct
Lobatto-pencil roots, and the exact degree-eight compatibility scalar.

The terminal-product test is paid on both original stage-eight branches.
A clean stage eight forces two literal operator identities and the checked
Hankel scalar cancellation. A defective stage eight forces one of two exact
quartic polynomial divisors. Polynomial scaling and quadratic
pseudo-remainders then give the terminal product zero even when the
head's quadratic coefficient or an affine equation coefficient vanishes.
The result contradicts the checked scalar-only
`RKCert.CompactResidue.sixOn_atlas_impossible`. No finite-field rows or
their certificates were replayed.

## Validation and additive prerequisites

Unchanged reviewed human basis: `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9), Mathlib v4.36.0
(fc4f59e577feb1a4956671bc04ac18aaaf8cd842). Prior source packets:
- Native one-off, SHA-256 `9d798055a44d0122534bfbfb028cdf32ed2597f6f3af6cbf70928cc9f553f52c`.
- Multi-low, `a69e1eb2b7ca05594d5075eb03e552ebd3804d8fbe37bc7b223a07073584bf9d`.
- Multi-high, `bb5bbedbe32c878debfdbc57d28bde7c9680e3636c6df584dbcbe39b0471f748`.
- Five-five, `748b13d0186b360667e8d5f0c371816dec5315ff565068992e951bcc0f518a92`.

Compile the twelve additive modules in the order recorded in
`checks/ORDER9-EXPLICIT-THIRTEEN-BUILD.txt` against those checked prerequisites
and the scalar objects. The separate audit has an independent consumer using
only the reviewed assumptions and prints the transitive axiom dependencies.
They are precisely `propext`, `Classical.choice`, and `Quot.sound`.
