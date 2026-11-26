# Literal minimal-width reverse blocks for a fixed strict SDIRK construction

These proofs concern the no-owner construction with a closed, zero-output-weight early block and a strict reverse block attached at distinct abscissae. The underlying RK convention and early construction are described in [Bulk absorption](../BULK-OWNER-ABSORPTION.md). They do not change the unrestricted strict SDIRK stage bounds.

- [Active tail and canonical abscissae](ACTIVE-TAIL.md): A trailing set of genuine output abscissae whose first strict continuations all vanish costs extra physical stages. For negative diagonal and the canonical reflected Laguerre abscissae, minimum width is impossible at even reverse budget. For balanced target orders the extra exclusions beyond the scalar and earlier parity tests occur at 12, 16, and 20.
- [Odd reverse budget](ODD-BRANCH.md): At minimum width, a hypothetical solution at the canonical abscissae has a three-dimensional cyclic space of model-zero numerical rows. These are necessary conditions, not an existence claim.
- [Marked source interpolation](MARKED-SOURCE.md): The exact rank of polynomial profiles realized by actual early-null rooted combinations after adjoining leaves at the root.

The proofs are algebraic, with sign and classical Laguerre hypotheses where indicated. No Lean verification is asserted.

## Mixed abscissae

- [Continuations through length three](MIXED-THREE.md): For balanced target orders \(12,16,20\), the respective late widths \(12,20,30\) admit real-algebraic stages satisfying every rooted condition through orders \(9,11,13\), and the stated length-three tests at the respective target budgets.
- [Continuations through length four](MIXED-FOUR.md): The same widths \(20,30\) for targets \(16,20\) also admit real-algebraic tableaux meeting all fourth-length tests and every rooted condition through orders \(12,14\). Full target order is not claimed.

## One root mark and the final condition

[One root mark and the final projected primitive](ONE-MARK.md) replaces the weaker saturation threshold in the marked-source proof with a single root mark. It identifies exact graded tests equivalent to rooted order for this construction and excludes the minimum late width for balanced odd targets at least nine. For balanced even targets, the stated real and extremal early-root assumptions force a negative first late abscissa at minimum width; in particular the nonnegative examples above at target sizes 12, 16, and 20 cannot reach their targets. Their proved shorter orders are unchanged.

- [First late abscissa and negative diagonals](FIRST-CLOCK-SIGN.md): Two genuine sources force a negative first late abscissa. The [prime-degree](NEGATIVE-ANCHOR.md) and [prime-interval](PRIME-INTERVAL.md) screens then rule out the balanced canonical minimum-width construction at orders 12, 16, 18, and 20 for any real negative diagonal. The hypotheses on the early block and distinct late abscissae remain essential.

## Adding one physical stage

- [An extra late stage or feeder](LATE.md) gives exact causal conditions for repairing the final word length. It also describes top-only geometries, which still need the lower word conditions.
- [An extra early stage](EARLY.md) gives an actual source space with two common zeros. When \(m\) is odd, one mark suffices; when \(m\) is even, the two-mark conclusion requires the stated rank condition.

## Lower-order contacts after a one-stage early change

- [Producing the double-factor inputs](ACTUAL-DOUBLE.md) supplies the missing even-\(m\) input by an actual unary extension, for the stated choice of the early Laguerre block and sampler.
- [An obstruction on a leading set of abscissae](LOWER-CUT.md) rules out generic minimum-width lower-word data at the stated balanced odd orders. It does not exclude exceptional prefixes. In the even-order argument, both parities use the additional complementary contacts.

## Exceptional prefixes

- [Odd reverse length](ODD-REALIZATION.md): Two real-algebraic choices for the next abscissa realize the selected primitive and clock contacts, with a true scalar rule and literal strict taps.
- [Even reverse length](EVEN-NO-GO.md): After the stated negative prefix the next abscissa is strictly interior, with at most \(r/2-1\) candidates at minimum late width.
- [Common strict taps](COMMON-TAPS.md): At the target-15 geometry the construction satisfies every rooted condition through order 11 on 33 stages. At target-19 geometry it satisfies every one through order 14 on 51 stages. The proved statements include additional higher contacts on the exceptional row, not full target order or a better unrestricted stage bound.
