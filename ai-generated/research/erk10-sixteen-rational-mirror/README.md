# Sixteen rational stages of exact ERK order ten

The [literal tableau](tableau.json) is strictly explicit, with
16 distinct stages and rational coefficients. This lowers the
verified rational upper bound from the
[17-stage witness](../erk10-seventeen-half-port/README.md) to
**16**. It does not close the real 14–15 gap.

The construction uses a rational doubled-clock dense prefix and a
mirrored reverse placement. In this witness the reflected donor is put
at a later adjustable receiver, rather than the first adjustable
receiver. The literal stores its horizon and raw reverse clock order.
The independent verifier does not need a correctness assumption for
the construction or a numerical tolerance.

## Exact replay and coefficient domain

Let `D` be the least common multiple of the coefficient denominators.
The [factor list](denominator-factors.json) specifies it exactly. The
[replay](replay.py) multiplies the entire tableau and weight vector by
`D`, independently generates all ordinary non-plane rooted trees
through order ten, and checks the integer numerator of every condition
against `D` raised to the number of vertices. All **1,205** conditions
hold.

Two order-eleven trees fail: the ten-leaf bush, and the tree whose
root has four leaf children and one child that is itself a five-leaf
bush. The factorial-scaled defects (value minus 1) are respectively
`-44183114898821/88516189142307000` and
`-506482972805483195311/82783211226952318425000`. Their reduced
numerators are coprime. Both denominators divide a power of `D`.

Consequently the **same tableau has exact order ten in every
nonzero commutative ring where D is a unit**. The cleared order-ten
identities specialize. If both order-eleven defects vanished, their
numerators would vanish as well, and integer Bézout would give 1=0.
This includes all characteristic-zero fields. The coefficient
denominator involves primes outside 10!, so the universal
factorial-only upper remains 17.

## Combined characteristic coverage

The newer [five-tableau rational portfolio](../erk10-sixteen-rational-portfolio/README.md)
covers every admissible local and finite-characteristic ring, including
the 21 primes listed below. The remainder of this section describes
only the initial two-construction comparison.

Combine this tableau with the [nineteen prime-power families](../erk10-sixteen-late-helper-primes/README.md).
For primes not dividing the coefficient denominator, this rational
tableau specializes at every power of the prime. Nine of its
denominator primes are covered separately by the prime-power families.
Consequently, among fields in which 10! is nonzero, the combined
16-stage construction covers every characteristic except at most the
following 21:

    97, 131, 167, 173, 263, 277, 419, 491, 613, 881, 1091,
    1307, 3137, 4111, 8747, 23117, 80273, 138323, 930617,
    2327539, 3595702991173.

An omitted characteristic is not an obstruction; it is not covered by
these tableaux. The Chinese remainder theorem also gives exact order in
any nonzero commutative ring of finite characteristic whose prime factors
avoid this list and 2, 3, 5, 7. Combine the separate literal coefficient
arrays over the prime-power components of its characteristic and then
map into the target ring. At least one nonzero component survives in a
nonzero target, so the order-eleven failure is retained. This does not
give a single tableau over the localization that inverts only 10!.

## Replay

From this directory:

    python3 -B replay.py
    sha256sum -c sources.sha256

This is an exact integer replay and mathematical ring transfer. It is
not yet an end-to-end native Lean certificate.
