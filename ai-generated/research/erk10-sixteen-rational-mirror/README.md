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

From this directory:

    python3 -B replay.py
    sha256sum -c sources.sha256

This is an exact integer replay and mathematical ring transfer. It is
not yet an end-to-end native Lean certificate.
