# Fifteen explicit stages through characteristic (17^{20})

The literal [fifteen-stage characteristic-17 tableau](../erk10-fifteen-f17/README.md)
has been lifted, compatibly, through every power (17^k) for
(1le kle20). The [largest literal](tableau.json) alone yields the
construction in each such characteristic by taking residues, including
over any nonzero commutative ring of that characteristic. A method
over all 17-adic precisions is not proved by this finite calculation.

The direct [standard-library replay](check_literal.py) checks all
1,205 rooted-tree conditions on the largest literal, its compatibility
modulo 17, and an order-eleven bush defect congruent to (8) modulo 17.
That defect is a unit modulo (17^{20}) and under every specialization.
For example, the same defect is (229) modulo (17^2=289).

For reconstruction, use NumPy and run
`python3 -B lift.py ../erk10-fifteen-f17/tableau.json /tmp/lifts.json`
from this directory. The script works with all 105 actual lower
triangular entries and 15 ordinary weights. It differentiates the
1,205 rooted order equations over (mathbb F_{17}) at the original
literal, obtains rank 111, and solves the resulting linear correction
problem at every precision by retaining one fixed pivot system and
setting nonpivot digits to zero. Starting with a solution modulo (m),
an increment (mmathbf x) changes the equations modulo (17m) by
(mJmathbf x); the omitted terms contain at least (m^2), a multiple
of (17m). After each update all actual rooted identities and the
bush defect are independently recomputed from the resulting coefficients;
large integer operations use Python's unbounded integers.

The exact finite certification is separate from any general lifting
theorem and does not change the real or universal factorial-localized
bounds.
