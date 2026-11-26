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
