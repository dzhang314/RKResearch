# Exact fifteen-stage ERK10 at 130 further primes

The [five-equation signed-pair construction](../erk10-fifteen-17-power/README.md)
works in **130 further prime characteristics** through 3000 beyond
the 61 known scalar Stepanov cases and the original characteristic 17
case. At each listed prime \(p\) it gives a strictly explicit 15-stage
method of exact order ten over \(\mathbb F_p\) and, by the checked
simple-root geometry and unit reconstruction, over \(\mathbb Z/p^k\)
for every \(k\ge1\), \(\mathbb Z_p\), and \(\mathbb Q_p\).
Each such prime also admits the construction over any nonzero
henselian local commutative ring of residue characteristic \(p\).
Prime-power literals transfer to every nonzero commutative ring of
that characteristic; the order-eleven bush defect is a unit.

These are verified successes, not a census of prime characteristics
where 15 stages are possible. The rational and real intervals and
the upper bound over the factorial localization do not change.

## The seed search and exact certificates

The compact univariate pressure equation suggests candidates:
solve for \(a\) in the degree-nine polynomial from the
[exact rational pressure calculation](../erk10-fifteen-rational-pressure-curve/README.md),
split the quadratic for the two last labels, and solve for
\(e\) and then \(c\) at a freely tried distinct \(d\).
The search uses no completeness assumption or numerical optimizer.
The criterion for success is independent of this discovery process:
each resulting six-coordinate seed satisfies the **five original
geometry equations**, has distinct ordinary sites and unit weights,
and has a unit five-variable Jacobian minor for coordinates
\((a,c,e,f,g)\) with \(d\) fixed. The seed data record that minor,
the donor response determinant, the two weighted observer/kernel
determinants, both read determinants and the nonzero dormant split.

The exact checker first verifies the 1,205 rooted equations and
the unit bush defect from the archived literal over the prime field.
It then checks the base reconstruction coefficientwise, lifts the
five geometry coordinates by one Hensel step, and reconstructs the
strict tableau modulo \(p^2\), holding the old seed clock choices
fixed as integers. Every inversion in that reconstruction is checked
to have nonzero residue, including the clock and quadrature divisions,
the actual read solves and the old opening decoder. It checks the
actual first two primitive residual rows determine the kernel, verifies
the remaining forward rows, and checks the augmented observer matrix
has unit determinant. Finally a separate ordinary rooted recurrence
again checks all 1,205 conditions plus the unit bush at \(p^2\) and
compatibility with the original prime-field literal. These steps give
260 independent literal replays.

The all-power and henselian assertions use the same mathematical
proof as at 17: the five polynomials have coefficients integral
after inverting only small fixed denominators (units for the listed
primes), so a simple seed lifts by the multivariate Hensel lemma.
Every causal reconstruction pivot just checked is a polynomial or
a ratio of units in that residue branch, so it stays a unit throughout
the lift. The literal six-read and anchored word proof applies over
the local coefficient ring, and the residue bush defect stays a unit.
The finite calculation at \(p^2\) is therefore a check of that
reconstruction, not the justification for extension to all powers.
These new coefficients are not themselves an end-to-end Lean
certificate; the characteristic-17 literal has a
[separate native certificate](../erk10-fifteen-f17/LEAN.md).

## Replay

From this directory, with SymPy available, run

    python3 -B search.py .. /tmp/signed-pair-primes.json 3000
    python3 -B check.py .. prime-literals.json /tmp/signed-pair-squares.json
    cmp /tmp/signed-pair-primes.json prime-literals.json
    cmp /tmp/signed-pair-squares.json square-literals.json
    sha256sum -c sources.sha256

The second command needs only the standard library and the two
existing geometry/reconstruction helpers; it checks all input data
without rerunning the search.
