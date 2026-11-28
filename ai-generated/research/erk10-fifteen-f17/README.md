# Fifteen explicit stages give exact order ten in characteristic 17

The [literal tableau](tableau.json) is strictly explicit and has
**exact order ten with fifteen stages** over the field with 17 elements.
This improves the [earlier sixteen-stage bound](../erk10-sixteen-f17/README.md).
It is not a proof that fourteen stages are impossible.

The archived construction uses the [five-row opening and cubic model
kernel](../erk10-five-opening-nonsplit-kernel/README.md), with an
exceptional reverse opening containing two pairs. Over the residue field
the model kernel is (X^3+6X^2-X); the reverse ordinates are
(0,-1,-1,-2,-2,2,8,9,4,6). The verification below uses only the
actual explicit tableau, not the decoder or the search architecture.

Run `python3 -B check_literal.py` with the standard library. It checks
all 1,205 rooted-tree equations through order ten, by increasing order.
For the eleven-vertex bush the weighted elementary value is (7), so
the cleared order defect is (11cdot7-1=8) modulo 17. See the
[independent replay](exact-replay.txt).

The unique unital map from (mathbb F_{17}) to any nonzero
commutative ring of characteristic 17 preserves the literal order
equations, and that defect maps to a unit, so exactness is preserved.
The bound therefore applies to every such ring, not just the field.
A lift to higher powers of 17 is not asserted. The real and rational
stage intervals and the universal factorial-localized bound are
unchanged. Native Lean certification of this literal is tracked
separately from the exact calculation here.
