# Twenty-one additional late-helper prime-power seeds for exact ERK10

This is an alternative prime-power construction, not an improvement
to the stage bound already provided by the
[five rational tableaux](../erk10-sixteen-rational-portfolio/README.md).
The 21 primes are the denominator primes of the
[first rational tableau](../erk10-sixteen-rational-mirror/README.md)
not covered by the original nineteen prime-power families.

The [seeds](seeds.json) use the same guarded
[late-helper method](../erk10-sixteen-late-helper-primes/README.md).
For each prime, the exact builder verifies its guard on the
terminal quadratic, the two simple roots at the early pair, the
literal eight-stage rational prefix and every pivot used at that
residue. The same proof gives an exact sixteen-stage order-ten
method at every power and over the corresponding p-adic ring
and field; its normalized next bush discrepancy remains a unit.
This is not an end-to-end native Lean lift.

From this directory:

    python3 -B replay.py
    python3 -B replay.py --exponent 3 --emit /tmp/rk-erk10-21
    sha256sum -c sources.sha256

The default verifies primality by trial division, regenerates the 42
tableaux at the first two powers and checks all 1,205 rooted conditions,
the stated next-order failure, and compatible reductions. The
independent tree enumerator does not use the construction.
